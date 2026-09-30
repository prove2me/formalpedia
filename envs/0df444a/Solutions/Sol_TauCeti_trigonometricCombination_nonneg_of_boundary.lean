-- Prove2me | solution 1 for TauCeti.trigonometricCombination_nonneg_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:09.04566+00:00
-- url     : https://prove2.me/submissions/806c3a42-e1a9-4b47-b63e-58d04fcccb6e

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_Trigonometric_NonnegCombination
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is a finite weighted cosine combination.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.

This is part of Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex

noncomputable section

variable {ι : Type*}



/-- The defining finite-sum formula for `trigonometricCombination`. -/
theorem TauCeti.trigonometricCombination_def (s : _root_.Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) :
    _root_.TauCeti.trigonometricCombination s c m z = ∑ i ∈ s, c i * (z ^ m i).re := (_root_.rfl)



variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}

/-- Nonnegativity of a trigonometric combination on the unit circle extends to the closed unit
disk. -/
theorem solution
    (h : _root_.TauCeti.IsNonnegativeTrigonometricCombination s c m) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ _root_.TauCeti.trigonometricCombination s c m z := by
  let f : ℂ → ℂ := fun w ↦ _root_.Complex.exp (-∑ i ∈ s, (c i : ℂ) * w ^ m i)
  have hf : _root_.Differentiable ℂ f := by
    dsimp [f]
    fun_prop
  have hnorm : ‖f z‖ ≤ 1 := _root_.Complex.norm_le_of_forall_mem_frontier_norm_le
      _root_.Metric.isBounded_ball hf.diffContOnCl (fun w hw ↦ by
        rw [_root_.frontier_ball (0 : ℂ) _root_.one_ne_zero, _root_.mem_sphere_zero_iff_norm] at hw
        simpa only [f, _root_.Complex.norm_exp, _root_.Complex.neg_re, _root_.Complex.re_sum, _root_.Complex.mul_re, _root_.Complex.ofReal_re, _root_.Complex.ofReal_im,
          _root_.MulZeroClass.zero_mul, _root_.sub_zero, _root_.Real.exp_le_one_iff, _root_.neg_nonpos,
          _root_.TauCeti.trigonometricCombination_def] using h w hw)
      (by rw [_root_.closure_ball (0 : ℂ) _root_.one_ne_zero, _root_.Metric.mem_closedBall,
        _root_.dist_zero_right]; exact hz)
  simpa only [f, _root_.Complex.norm_exp, _root_.Complex.neg_re, _root_.Complex.re_sum, _root_.Complex.mul_re, _root_.Complex.ofReal_re, _root_.Complex.ofReal_im,
    _root_.MulZeroClass.zero_mul, _root_.sub_zero, _root_.Real.exp_le_one_iff, _root_.neg_nonpos, _root_.TauCeti.trigonometricCombination_def] using hnorm



end

end TauCeti

end
end
