-- Prove2me | solution 1 for ThreeSumApsp.Spec.abs_dpValue_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:24:07.412986+00:00
-- url     : https://prove2.me/submissions/a3ace352-4676-4158-b548-43e6308f8f94

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma6
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Lemma 6: Schönhage's identity

Sections 2.1 and 2.2. After Strassen's identity (equation (1)), which the paper
recalls, this file treats Schönhage's. It has ten terms `λ`, each the product of a linear form `φ_λ`
in the seven left variables, a linear form `ψ_λ` in the seven right variables and a linear form
`χ_λ` in the ten output variables. Lemma 6 says that `∑_λ φ_λ ψ_λ χ_λ = G + E`, an identity of
polynomials in the 24 variables: `G` holds the outer product and the inner product that are wanted,
and `E` is an error.

* A linear form is the vector of its coefficients. `formL`, `formR` and `formO` turn it into a
  polynomial, and they are linear (`formL_eq_linearCombination` and its two companions).
* The proof of `lemma_6` is the paper's. The coefficient of `z_ij` comes only from the term `P_ij`.
  In the coefficient of `z₀` the products `x_i y_j` cancel, the cross terms vanish because the
  columns of `p̂` and the rows of `q̂` sum to zero (`pHat_column_sum`, `qHat_row_sum`), and what
  remains is the inner product (`sum_pHat_mul_qHat`).
* Second observation after the lemma: every term contributes to `z₀`, and only `P_ij` contributes to
  `z_ij` (`Term.contributes_z0`, `Term.contributes_z_iff`).

The later files on Section 2 use the second observation and the coefficients of the forms; none of
their proofs uses `lemma_6`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp















/-! ### The alphabets -/










































/-- Section 2.2: "Schönhage's identity has ten terms". -/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]







/-! ### Linear forms as polynomials -/























































/-! ### Lemma 6 -/



































/-! ### Which terms contribute to which output variables -/




































end ThreeSumApsp

end



/-!
# Bounds on the partial sums (proof of Theorem 30, "Word size")

"every value we compute is a sum of at most 10^m products of two such numbers".  A routine that adds
up numbers one after the other holds, at every moment, the sum of an initial part of a list.  This
file bounds all these sums, for two encodings whose entries are at most A and B in absolute value.

* What the dynamic program of Lemma 29 computes for a cube with e stars is at most 10^e A B
  (`abs_dpValue_le`), and so is every sum of an initial part of the ten values that it adds up
  for the cube (`abs_dp_partial_sum_le`).
* The numbers that a query adds up stand for disjoint sets of leaves contributing to its output
  string η (the paper's w), of which there are 10^m (`Lemma28.card_leaves`); so every sum of an
  initial part of them is at most 10^m A B (`abs_query_partial_sum_le`).
-/

public section

namespace ThreeSumApsp.Spec

variable {L : ℕ} {encA encB : Leaf L → ℤ} {A B : ℤ} (hA : ∀ τ, |encA τ| ≤ A)
  (hB : ∀ τ, |encB τ| ≤ B)

include hA hB

/-! ## The dynamic program of Lemma 29 -/

/-- A B ≥ 0 for bounds A, B on the two arrays. -/
theorem mul_nonneg_of_abs_le : 0 ≤ A * B :=
  mul_nonneg ((abs_nonneg _).trans (hA fun _ => Term.P0))
    ((abs_nonneg _).trans (hB fun _ => Term.P0))

/-- The product at a leaf is at most A B in absolute value. -/
private theorem abs_mul_le (τ : Leaf L) : |encA τ * encB τ| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul (hA τ) (hB τ) (abs_nonneg _) ((abs_nonneg _).trans (hA τ))

/-- What the dynamic program computes at depth e is at most 10^e A B in absolute value. -/
theorem abs_dpValue_le_sourceProof (e : ℕ) (π : Cube L) : |dpValue encA encB e π| ≤ 10 ^ e * (A * B) := by
  have hAB := mul_nonneg_of_abs_le hA hB
  induction e generalizing π with
  | zero =>
    rw [dpValue, pow_zero, one_mul]
    exact abs_mul_le hA hB _
  | succ e ih =>
    rw [dpValue]
    split_ifs with h
    · calc |∑ lam : Term, dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)|
          ≤ ∑ lam : Term, |dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _lam : Term, 10 ^ e * (A * B) := Finset.sum_le_sum fun lam _ => ih _
        _ = 10 ^ (e + 1) * (A * B) := by
            rw [Finset.sum_const, Finset.card_univ, card_term, nsmul_eq_mul]
            push_cast
            ring
    · rw [abs_zero]
      positivity




























/-! ## A query -/




























end ThreeSumApsp.Spec

end


theorem solution : ∀ {L : Nat} {encA encB : ThreeSumApsp.Leaf L → Int} {A B : Int},
  (∀ (τ : ThreeSumApsp.Leaf L),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (encA τ)) A) →
    (∀ (τ : ThreeSumApsp.Leaf L),
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (encB τ)) B) →
      ∀ (e : Nat) (π : ThreeSumApsp.Cube L),
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup (@ThreeSumApsp.dpValue L encA encB e π))
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10))) e)
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) A B)) := by
  exact @ThreeSumApsp.Spec.abs_dpValue_le_sourceProof

#print axioms solution
