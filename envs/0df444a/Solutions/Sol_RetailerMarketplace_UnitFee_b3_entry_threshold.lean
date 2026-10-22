-- Prove2me | solution 1 for RetailerMarketplace.UnitFee.b3_entry_threshold
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:26:10.590979+00:00
-- url     : https://prove2.me/submissions/b3e6cebb-31cf-48c7-9780-0c6ed5471df6

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

set_option autoImplicit false
open MeasureTheory RetailerMarketplace.UnitFee

theorem solution (c f t lam : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (ht : 0 ≤ t) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (v : ℝ) :
    (0 < piSBT_T c f t v ↔ vT c f t < v) ∧
    (0 < pbarT c f t lam v * (1 - f) - c - t ↔ vT c f t < v) ∧
    (v ∈ mp c f t ↔ vT c f t ≤ v) := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl1, hl2⟩ := hlam
  have h1 : 0 < 1 - f := by linarith
  have hD : 0 < 1 - f * (1 - lam) := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold piSBT_T vT
    rw [div_lt_iff₀ h1]; constructor <;> intro h <;> nlinarith
  · have key : pbarT c f t lam v * (1 - f) - c - t
        = lam * ((1 - f) * v - (c + t)) / (1 - f * (1 - lam)) := by
      have hP : pbarT c f t lam v * (1 - f * (1 - lam)) = lam * v + (1 - lam) * (c + t) := by
        unfold pbarT; exact div_mul_cancel₀ _ hD.ne'
      rw [eq_div_iff hD.ne']
      linear_combination (1 - f) * hP
    rw [key]; unfold vT; rw [div_lt_iff₀ h1]
    rw [div_pos_iff_of_pos_right hD]
    constructor <;> intro h
    · by_contra hh; push_neg at hh
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ lam) (by linarith : 0 ≤ (c + t) - v * (1 - f))]
    · have : 0 < (1 - f) * v - (c + t) := by linarith
      exact mul_pos (by linarith) this
  · unfold mp vT
    rw [div_le_iff₀ h1]; simp only [Set.mem_setOf_eq]
