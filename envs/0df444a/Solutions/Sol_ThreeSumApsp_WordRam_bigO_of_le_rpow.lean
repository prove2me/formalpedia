-- Prove2me | solution 1 for ThreeSumApsp.WordRam.bigO_of_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:50:33.711271+00:00
-- url     : https://prove2.me/submissions/66b38a7a-8527-49c2-b02e-8fba0d4e831c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam

/-- For a rational `r = p/q ≥ 0`: `(n^r)^q = n^p`. -/
theorem rpow_pow_den {r : ℚ} (hr0 : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr0))
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hmul : (r : ℝ) * (r.den : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
    rw [Rat.cast_def, hnum]
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hmul, Real.rpow_natCast]

/-- A function with `T(n) ≤ C n^r` from `n = 2` on is `O(n^r)` in the sense of the end statement. -/
theorem bigO_of_le_rpow_sourceProof {C : ℝ} {r : ℚ} (hr0 : 0 ≤ r) {T : ℕ → ℕ}
    (hT : ∀ n : ℕ, 2 ≤ n → (T n : ℝ) ≤ C * (n : ℝ) ^ (r : ℝ)) : EndStatement.BigO T r := by
  refine ⟨⌈|C| ^ r.den⌉₊, fun n hn => ?_⟩
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hreal : (T n : ℝ) ^ r.den ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
    calc (T n : ℝ) ^ r.den
        ≤ (|C| * (n : ℝ) ^ (r : ℝ)) ^ r.den :=
          pow_le_pow_left₀ (Nat.cast_nonneg _)
            ((hT n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hrpow)) _
      _ = |C| ^ r.den * (n : ℝ) ^ r.num.toNat := by rw [mul_pow, rpow_pow_den hr0]
      _ ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact_mod_cast hreal






























end ThreeSumApsp.WordRam

end


theorem solution : ∀ {C : Real} {r : Rat},
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) r →
    ∀ {T : Nat → Nat},
      (∀ (n : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (T n))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@Nat.cast.{0} Real Real.instNatCast n) (@Rat.cast.{0} Real Real.instRatCast r)))) →
        EndStatement.BigO T r := by
  exact @ThreeSumApsp.WordRam.bigO_of_le_rpow_sourceProof

#print axioms solution
