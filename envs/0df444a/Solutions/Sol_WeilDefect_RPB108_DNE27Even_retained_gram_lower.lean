-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.retained_gram_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:03:57.948825+00:00
-- url     : https://prove2.me/submissions/81f7ad4b-9148-462d-939b-c0b18c014dbc

import Theorems.Thm_WeilDefect_RPB108_complex_gram_lower
import Theorems.Thm_WeilDefect_RPB108_scaled_gram_difference
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27RetainedEnergy_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem gram_scales_pos (i : Fin 3) : 0 < gramScales i := by
  fin_cases i <;> norm_num [gramScales, scales, Matrix.cons_val_two]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem retained_margin_certificate (i : Fin 3) :
    rowMargins retainedDiagonalLower retainedOffBounds i = retainedPublishedMargins i ∧
    retainedLower ≤ retainedPublishedMargins i := by
  fin_cases i <;> norm_num [rowMargins, retainedDiagonalLower, retainedOffBounds,
    retainedPublishedMargins, gramScales, scales, Matrix.cons_val_two, nativeLower, retainedLower]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem retained_off_certificate (i j : Fin 3) (hij : i ≠ j) :
    -offWeights retainedOffBounds i j ≤ gramScales i*gramScales j*nativeLower i j ∧
    gramScales i*gramScales j*nativeUpper i j ≤ offWeights retainedOffBounds i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [offWeights, retainedOffBounds, gramScales, scales, Matrix.cons_val_two, nativeLower, nativeUpper] at *
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem retained_off_nonneg (i : Fin 3) : 0 ≤ retainedOffBounds i := by
  fin_cases i <;> norm_num [retainedOffBounds]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108
/-- Exact column congruence for the retained quadratic form. -/
theorem scaled_retained_gram (V : Fin 3 → Fin 3 → ℝ) (s : Fin 3 → ℝ)
    (z : Fin 3 → ℂ) :
    complexGram (fun i j => s i*s j*V i j) z =
      complexGram V (fun i => (s i : ℂ)*z i) := by
  simpa [complexGram] using scaled_gram_difference V (fun _ _ => 0) s 1 z
end WeilDefect.RPB108

theorem solution (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 3 → ℂ) :
    retainedLower*(∑ i, ‖z i‖^2) ≤
      complexGram V (fun i => (gramScales i : ℂ)*z i) := by
  let A := fun i j => gramScales i*gramScales j*V i j
  have hs (i j : Fin 3) : 0 ≤ gramScales i*gramScales j :=
    mul_nonneg (gram_scales_pos i).le (gram_scales_pos j).le
  have hd (i : Fin 3) : retainedDiagonalLower i ≤ A i i :=
    mul_le_mul_of_nonneg_left (hV i i).1 (hs i i)
  have ha (i j : Fin 3) (hij : i ≠ j) : |A i j| ≤ offWeights retainedOffBounds i j := by
    apply abs_le.mpr
    constructor
    · exact (retained_off_certificate i j hij).1.trans
        (mul_le_mul_of_nonneg_left (hV i j).1 (hs i j))
    · exact (mul_le_mul_of_nonneg_left (hV i j).2 (hs i j)).trans
        (retained_off_certificate i j hij).2
  have bound := complex_gram_lower A retainedDiagonalLower retainedOffBounds
    retained_off_nonneg hd ha z
  have hf : retainedLower*(∑ i, ‖z i‖^2) ≤
      ∑ i, rowMargins retainedDiagonalLower retainedOffBounds i*‖z i‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [(retained_margin_certificate i).1]
    exact mul_le_mul_of_nonneg_right (retained_margin_certificate i).2 (sq_nonneg _)
  have he := hf.trans bound
  simpa only [A, scaled_retained_gram] using he
