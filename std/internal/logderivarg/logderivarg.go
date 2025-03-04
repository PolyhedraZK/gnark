// Package logderivarg implements log-derivative argument.
//
// The log-derivative argument was described in [Haböck22] as an improvement
// over [BCG+18]. In [BCG+18], it was shown that to show inclusion of a multiset
// S in T, one can show
//
//	∏_{f∈F} (x-f)^count(f, S) == ∏_{s∈S} x-s,
//
// where function `count` counts the number of occurrences of f in S. The problem
// with this approach is the high cost for exponentiating the left-hand side of
// the equation. However, in [Haböck22] it was shown that when avoiding the
// poles, we can perform the same check for the log-derivative variant of the
// equation:
//
//	∑_{f∈F} count(f,S)/(x-f) == ∑_{s∈S} 1/(x-s).
//
// Additionally, when the entries of both S and T are vectors, then instead we
// can check random linear combinations. So, when F is a matrix and S is a
// multiset of its rows, we first generate random linear coefficients (r_1, ...,
// r_n) and check
//
//	∑_{f∈F} count(f,S)/(x-∑_{i∈[n]}r_i*f_i) == ∑_{s∈S} 1/(x-∑_{i∈[n]}r_i*s_i).
//
// This package is a low-level primitive for building more extensive gadgets. It
// only checks the last equation, but the tables and queries should be built by
// the users.
//
// NB! The package doesn't check that the entries in table F are unique.
//
// [BCG+18]: https://eprint.iacr.org/2018/380
// [Haböck22]: https://eprint.iacr.org/2022/1530
package logderivarg

// TODO: we handle both constant and variable tables. But for variable tables we
// have to ensure that all the table entries differ! Right now isn't a problem
// because everywhere we build we also have indices which ensure uniqueness. I
// guess the best approach is to have safe and unsafe versions where the safe
// version performs additional sorting. But that is really really expensive as
// we have to show that all sorted values ara monotonically increasing.

import (
	"errors"
	"fmt"
	"math/big"

	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/std/multicommit"
)

func init() {
	solver.RegisterHint(GetHints()...)
}

// GetHints returns all hints used in this package
func GetHints() []solver.Hint {
	return []solver.Hint{countHint}
}

// Table is a vector of vectors.
type Table [][]frontend.Variable

// AsTable returns a vector as a single-column table.
func AsTable(vector []frontend.Variable) Table {
	ret := make([][]frontend.Variable, len(vector))
	for i := range vector {
		ret[i] = []frontend.Variable{vector[i]}
	}
	return ret
}

// Build builds the argument using the table and queries. If both table and
// queries are multiple-column, then also samples coefficients for the random
// linear combinations.
func Build(api frontend.API, table Table, queries Table) error {
	if len(table) == 0 {
		return errors.New("table empty")
	}
	nbRow := len(table[0])
	constTable := true
	countInputs := []frontend.Variable{len(table), nbRow}
	for i := range table {
		if len(table[i]) != nbRow {
			return errors.New("table row length mismatch")
		}
		if constTable {
			for j := range table[i] {
				if _, isConst := api.Compiler().ConstantValue(table[i][j]); !isConst {
					constTable = false
				}
			}
		}
		countInputs = append(countInputs, table[i]...)
	}
	for i := range queries {
		if len(queries[i]) != nbRow {
			return errors.New("query row length mismatch")
		}
		countInputs = append(countInputs, queries[i]...)
	}
	exps, err := api.NewHint(countHint, len(table), countInputs...)
	if err != nil {
		return fmt.Errorf("hint: %w", err)
	}

	var toCommit []frontend.Variable
	if !constTable {
		for i := range table {
			toCommit = append(toCommit, table[i]...)
		}
	}
	for i := range queries {
		toCommit = append(toCommit, queries[i]...)
	}
	toCommit = append(toCommit, exps...)

	//rewrite logup to avoid direct division operation
	multicommit.WithCommitment(api, func(api frontend.API, commitment frontend.Variable) error {
		challenge := commitment
		rowCoeffs := GetColumnRandomness(api, nbRow, FullRandom)
		table_poly := make([]RationalNumber, len(table))
		for i := range table {
			table_poly[i] = RationalNumber{
				Numerator:   exps[i],
				Denominator: api.Sub(challenge, randLinearCombination(api, rowCoeffs, table[i])),
			}
		}
		table_poly_at_alpha := SumRationalNumbers(api, table_poly)

		query_poly := make([]RationalNumber, len(queries))
		for i := range queries {
			query_poly[i] = RationalNumber{
				Numerator:   1,
				Denominator: api.Sub(challenge, randLinearCombination(api, rowCoeffs, queries[i])),
			}
		}
		query_poly_at_alpha := SumRationalNumbers(api, query_poly)
		api.AssertIsEqual(
			api.Mul(table_poly_at_alpha.Numerator, query_poly_at_alpha.Denominator),
			api.Mul(query_poly_at_alpha.Numerator, table_poly_at_alpha.Denominator),
		)
		return nil
	}, toCommit...)
	return nil
}

type ColumnCombineOptions int

const (
	Poly = iota
	FullRandom
)

func SimpleMin(a int, b int) int {
	if a < b {
		return a
	} else {
		return b
	}
}
func GetColumnRandomness(api frontend.API, n_columns int, column_combine_options ColumnCombineOptions) []frontend.Variable {
	var randomness = make([]frontend.Variable, n_columns)
	committer, ok := api.Compiler().(frontend.Committer)
	if !ok {
		panic("compiler doesn't implement frontend.Committer")
	}
	if column_combine_options == Poly {
		beta, err := committer.Commit([]frontend.Variable{}...)
		if err != nil {
			panic(err)
		}
		randomness[0] = 1
		randomness[1] = beta

		// Hopefully this will generate fewer layers than sequential pows
		max_deg := int(1)
		for max_deg < n_columns {
			for i := max_deg + 1; i <= SimpleMin(max_deg*2, n_columns-1); i++ {
				randomness[i] = api.Mul(randomness[max_deg], randomness[i-max_deg])
			}
			max_deg *= 2
		}

		// Debug Code:
		// for i := 1; i < n_columns; i++ {
		// 	api.AssertIsEqual(randomness[i], api.Mul(randomness[i - 1], beta))
		// }

	} else if column_combine_options == FullRandom {
		randomness[0] = 1
		var err error
		for i := 1; i < int(n_columns); i++ {
			randomness[i], err = committer.Commit([]frontend.Variable{}...)
			if err != nil {
				panic(err)
			}
		}
	} else {
		panic("Unknown poly combine options")
	}
	return randomness
}

type RationalNumber struct {
	Numerator   frontend.Variable
	Denominator frontend.Variable
}

func (r *RationalNumber) Add(api frontend.API, other *RationalNumber) RationalNumber {
	return RationalNumber{
		Numerator:   api.Add(api.Mul(r.Numerator, other.Denominator), api.Mul(other.Numerator, r.Denominator)),
		Denominator: api.Mul(r.Denominator, other.Denominator),
	}
}

// Construct a binary summation tree to sum all the values
func SumRationalNumbers(api frontend.API, rs []RationalNumber) RationalNumber {
	n := len(rs)
	if n == 0 {
		return RationalNumber{Numerator: 0, Denominator: 1}
	}

	cur := rs
	next := make([]RationalNumber, 0)

	for n > 1 {
		n >>= 1
		for i := 0; i < n; i++ {
			next = append(next, cur[i*2].Add(api, &cur[i*2+1]))
		}
		cur = next
		next = next[:0]
	}

	if len(cur) != 1 {
		panic("Summation code may be wrong.")
	}

	return cur[0]
}
func randLinearCoefficients(api frontend.API, nbRow int, commitment frontend.Variable) (rowCoeffs []frontend.Variable, challenge frontend.Variable) {
	hasher, err := mimc.NewMiMC(api)
	if err != nil {
		panic(err)
	}
	rowCoeffs = make([]frontend.Variable, nbRow)
	rowCoeffs[0] = 1
	for i := 1; i < nbRow; i++ {
		hasher.Reset()
		hasher.Write(i+1, commitment)
		rowCoeffs[i] = hasher.Sum()
	}
	return rowCoeffs, commitment
}

func randLinearCombination(api frontend.API, rowCoeffs []frontend.Variable, row []frontend.Variable) frontend.Variable {
	if len(rowCoeffs) != len(row) {
		panic("coefficient count mismatch")
	}
	var res frontend.Variable = 0
	for i := range rowCoeffs {
		res = api.Add(res, api.Mul(rowCoeffs[i], row[i]))
	}
	return res
}

func countHint(m *big.Int, inputs []*big.Int, outputs []*big.Int) error {
	if len(inputs) <= 2 {
		return fmt.Errorf("at least two input required")
	}
	if !inputs[0].IsInt64() {
		return fmt.Errorf("first element must be length of table")
	}
	nbTable := int(inputs[0].Int64())
	if !inputs[1].IsInt64() {
		return fmt.Errorf("first element must be length of row")
	}
	nbRow := int(inputs[1].Int64())
	if len(inputs) < 2+nbTable {
		return fmt.Errorf("input doesn't fit table")
	}
	if len(outputs) != nbTable {
		return fmt.Errorf("output not table size")
	}
	if (len(inputs)-2-nbTable*nbRow)%nbRow != 0 {
		return fmt.Errorf("query count not full integer")
	}
	nbQueries := (len(inputs) - 2 - nbTable*nbRow) / nbRow
	if nbQueries <= 0 {
		return fmt.Errorf("at least one query required")
	}
	nbBytes := (m.BitLen() + 7) / 8
	buf := make([]byte, nbBytes*nbRow)
	histo := make(map[string]int64, nbTable) // string key as big ints not comparable
	for i := 0; i < nbTable; i++ {
		for j := 0; j < nbRow; j++ {
			inputs[2+nbRow*i+j].FillBytes(buf[j*nbBytes : (j+1)*nbBytes])
		}
		k := string(buf)
		if _, ok := histo[k]; ok {
			return fmt.Errorf("duplicate key")
		}
		histo[k] = 0
	}
	for i := 0; i < nbQueries; i++ {
		for j := 0; j < nbRow; j++ {
			inputs[2+nbRow*nbTable+nbRow*i+j].FillBytes(buf[j*nbBytes : (j+1)*nbBytes])
		}
		k := string(buf)
		v, ok := histo[k]
		if !ok {
			return fmt.Errorf("query element not in table")
		}
		v++
		histo[k] = v
	}
	for i := 0; i < nbTable; i++ {
		for j := 0; j < nbRow; j++ {
			inputs[2+nbRow*i+j].FillBytes(buf[j*nbBytes : (j+1)*nbBytes])
		}
		outputs[i].Set(big.NewInt(histo[string(buf)]))
	}
	return nil
}
