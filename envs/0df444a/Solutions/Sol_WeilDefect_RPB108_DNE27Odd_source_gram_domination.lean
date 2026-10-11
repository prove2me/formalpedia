-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.source_gram_domination
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:03:57.636915+00:00
-- url     : https://prove2.me/submissions/062a456e-f117-4dc1-9c31-cd4dafe16fb5

import Theorems.Thm_WeilDefect_RPB108_complex_gram_lower
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108.DNE27Odd
theorem complete_off_certificate (i j : Fin 3) (hij : i ≠ j) :
    -offWeights offBounds i j ≤ scaledLower i j ∧
    scaledUpper i j ≤ offWeights offBounds i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [offWeights, offBounds, scaledLower, scaledUpper, gramScales,
      scales, Matrix.cons_val_two, rho, nativeLower, nativeUpper, gramLower, gramUpper] at *
end WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108.DNE27Odd
theorem gram_scales_pos (i : Fin 3) : 0 < gramScales i := by
  fin_cases i <;> norm_num [gramScales, scales, Matrix.cons_val_two]
end WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108.DNE27Odd
theorem off_bounds_nonneg (i : Fin 3) : 0 ≤ offBounds i := by
  fin_cases i <;> norm_num [offBounds]
end WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108.DNE27Odd
theorem rho_nonneg : 0 ≤ rho := by norm_num [rho]
end WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108.DNE27Odd
theorem row_margin_certificate (i : Fin 3) :
    rowMargins diagonalLower offBounds i = publishedMargins i ∧
    0 < publishedMargins i := by
  fin_cases i <;> norm_num [rowMargins, diagonalLower, scaledLower,
    gramScales, scales, Matrix.cons_val_two, rho, nativeLower, gramUpper, offBounds, publishedMargins]
end WeilDefect.RPB108.DNE27Odd

theorem solution (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (z : Fin 3 → ℂ) :
    (∑ i, publishedMargins i*‖z i‖^2) ≤
      complexGram (fun i j => gramScales i*gramScales j*(rho*V i j-G i j)) z := by
  let A := fun i j => gramScales i*gramScales j*(rho*V i j-G i j)
  have hb (i j : Fin 3) : scaledLower i j ≤ A i j ∧ A i j ≤ scaledUpper i j := by
    have hs : 0 ≤ gramScales i*gramScales j := mul_nonneg (gram_scales_pos i).le (gram_scales_pos j).le
    constructor
    · exact mul_le_mul_of_nonneg_left
        (sub_le_sub (mul_le_mul_of_nonneg_left (hV i j).1 rho_nonneg) (hG i j).2) hs
    · exact mul_le_mul_of_nonneg_left
        (sub_le_sub (mul_le_mul_of_nonneg_left (hV i j).2 rho_nonneg) (hG i j).1) hs
  have hd (i : Fin 3) : diagonalLower i ≤ A i i := (hb i i).1
  have ha (i j : Fin 3) (hij : i ≠ j) : |A i j| ≤ offWeights offBounds i j := by
    exact abs_le.mpr ⟨(complete_off_certificate i j hij).1.trans (hb i j).1,
      (hb i j).2.trans (complete_off_certificate i j hij).2⟩
  have bound := complex_gram_lower A diagonalLower offBounds off_bounds_nonneg hd ha z
  simpa only [(row_margin_certificate _).1] using bound
