-- Prove2me | solution 1 for TauCeti.sum_re_neg_log_one_sub_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:31:54.006795+00:00
-- url     : https://prove2.me/submissions/a68f24cb-830a-4ac8-8935-fc5123fade57

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_Trigonometric_NonnegCombination
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Theorems.Thm_TauCeti_trigonometricCombination_nonneg_of_boundary

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



/-- Unit-circle nonnegativity of a trigonometric combination transfers to the Taylor series of
`-log (1 - z)` throughout the closed unit disk. -/
theorem solution
    (h : _root_.TauCeti.IsNonnegativeTrigonometricCombination s c m)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ i ∈ s, c i * (-_root_.Complex.log (1 - a * z ^ m i)).re := by
  have ha : ‖(a : ℂ)‖ < 1 := by
    simpa only [_root_.Complex.norm_real, _root_.Real.norm_of_nonneg ha₀] using ha₁
  have haz (i : ι) : ‖(a : ℂ) * z ^ m i‖ < 1 := by
    rw [_root_.norm_mul, _root_.norm_pow]
    calc
      ‖(a : ℂ)‖ * ‖z‖ ^ m i ≤ ‖(a : ℂ)‖ * 1 :=
        _root_.mul_le_mul_of_nonneg_left (_root_.pow_le_one₀ (_root_.norm_nonneg z) hz) (_root_.norm_nonneg _)
      _ < 1 := by simpa only [_root_.mul_one] using ha
  have hsum : _root_.HasSum
      (fun n : ℕ ↦ ∑ i ∈ s, c i * ((((a : ℂ) * z ^ m i) ^ n / n).re))
      (∑ i ∈ s, c i * (-_root_.Complex.log (1 - a * z ^ m i)).re) := by
    exact _root_.hasSum_sum fun i _ ↦
      (_root_.Complex.hasSum_re (_root_.Complex.hasSum_taylorSeries_neg_log (haz i))).mul_left (c i)
  rw [← hsum.tsum_eq]
  refine _root_.tsum_nonneg fun n ↦ ?_
  have hrewrite :
      (∑ i ∈ s, c i * ((((a : ℂ) * z ^ m i) ^ n / n).re)) =
        (a ^ n / (n : ℝ)) * _root_.TauCeti.trigonometricCombination s c m (z ^ n) := by
    simp only [_root_.mul_pow, ← _root_.Complex.ofReal_pow, _root_.Complex.div_natCast_re, _root_.Complex.ofReal_re, _root_.Complex.mul_re, _root_.Complex.ofReal_im, _root_.MulZeroClass.zero_mul,
      _root_.sub_zero, _root_.TauCeti.trigonometricCombination_def, _root_.Finset.mul_sum]
    apply _root_.Finset.sum_congr _root_.rfl
    intro i _
    rw [← _root_.pow_mul, _root_.mul_comm (m i) n]
    ring_nf
  rw [hrewrite]
  refine _root_.mul_nonneg (_root_.div_nonneg (_root_.pow_nonneg ha₀ n) (_root_.Nat.cast_nonneg n)) ?_
  exact _root_.TauCeti.trigonometricCombination_nonneg_of_boundary h
    (by rw [_root_.norm_pow]; exact _root_.pow_le_one₀ (_root_.norm_nonneg z) hz)

end

end TauCeti

end
end
