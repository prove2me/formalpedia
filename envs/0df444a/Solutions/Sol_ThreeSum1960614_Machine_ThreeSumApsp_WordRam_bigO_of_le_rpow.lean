-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:31.140297+00:00
-- url     : https://prove2.me/submissions/11494a8c-7508-49dc-9180-8bf47f57b788

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSumApsp.WordRam


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









end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

section

/-- A function with `T(n) ≤ C n^r` from `n = 2` on is `O(n^r)` in the sense of the end statement. -/
theorem ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow__implementation_2c76354196 {C : ℝ} {r : ℚ} (hr0 : 0 ≤ r) {T : ℕ → ℕ}
    (hT : ∀ n : ℕ, 2 ≤ n → (T n : ℝ) ≤ C * (n : ℝ) ^ (r : ℝ)) : _root_.EndStatement.BigO T r := by
  refine ⟨⌈|C| ^ r.den⌉₊, fun n hn => ?_⟩
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hreal : (T n : ℝ) ^ r.den ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
    calc (T n : ℝ) ^ r.den
        ≤ (|C| * (n : ℝ) ^ (r : ℝ)) ^ r.den :=
          pow_le_pow_left₀ (Nat.cast_nonneg _)
            ((hT n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hrpow)) _
      _ = |C| ^ r.den * (n : ℝ) ^ r.num.toNat := by rw [mul_pow, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.rpow_pow_den hr0]
      _ ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact_mod_cast hreal
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow__implementation_2c76354196) := (@ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow__implementation_2c76354196)

#print axioms solution
