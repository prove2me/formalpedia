-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.strict_source_gram_domination
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:08:58.966745+00:00
-- url     : https://prove2.me/submissions/211333ce-cba4-4f70-978f-6b1b7ba676e9

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_source_gram_domination
import Theorems.Thm_WeilDefect_RPB108_scaled_gram_difference
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem rho_lt_one : rho < 1 := by norm_num [rho]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem row_margin_certificate (i : Fin 3) :
    rowMargins diagonalLower offBounds i = publishedMargins i ∧
    0 < publishedMargins i := by
  fin_cases i <;> norm_num [rowMargins, diagonalLower, scaledLower,
    gramScales, scales, Matrix.cons_val_two, rho, nativeLower, gramUpper, offBounds, publishedMargins]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108
/-- Positive row weights give a strict gap for every nonzero complex vector. -/
theorem positive_weighted_norm_sq (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z : Fin 3 → ℂ) (hz : z ≠ 0) : 0 < ∑ i, m i*‖z i‖^2 := by
  have hi : ∃ i, z i ≠ 0 := by
    by_contra! h
    apply hz
    funext i
    exact h i
  obtain ⟨i,hi⟩ := hi
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hm j).le (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ _, mul_pos (hm i) (sq_pos_of_pos (norm_pos_iff.mpr hi))⟩
end WeilDefect.RPB108

theorem solution (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (z : Fin 3 → ℂ) (hz : z ≠ 0) :
    complexGram G (fun i => (gramScales i : ℂ)*z i) <
      rho*complexGram V (fun i => (gramScales i : ℂ)*z i) := by
  have hp := positive_weighted_norm_sq publishedMargins
    (fun i => (row_margin_certificate i).2) z hz
  have h := source_gram_domination V G hV hG z
  rw [scaled_gram_difference] at h
  linarith
