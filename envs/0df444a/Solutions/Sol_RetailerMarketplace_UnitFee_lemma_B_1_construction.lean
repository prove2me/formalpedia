-- Prove2me | solution 1 for RetailerMarketplace.UnitFee.lemma_B_1_construction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:26:11.51944+00:00
-- url     : https://prove2.me/submissions/4617116c-d7c5-40a5-addc-b4f8acebfd03

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

set_option autoImplicit false
open MeasureTheory RetailerMarketplace.UnitFee

theorem solution (c fs ts ε f' t' : ℝ) (hc : 0 < c)
    (hfs : fs ∈ Set.Ico (0 : ℝ) 1) (hε : 0 < ε) (hεts : ε < ts)
    (hf' : f' = (ε + fs * (c + ts - ε)) / (c + ts)) (ht' : t' = ts - ε) :
    0 < t' ∧ fs < f' ∧ f' < 1 ∧ vT c f' t' = vT c fs ts ∧ mp c f' t' = mp c fs ts := by
  obtain ⟨hf0, hf1⟩ := hfs
  have hpos : 0 < c + ts := by linarith
  have h1 : 0 < 1 - fs := by linarith
  have e1 : 1 - f' = (1 - fs) * (c + ts - ε) / (c + ts) := by
    rw [hf']; field_simp; ring
  have hc' : 0 < c + ts - ε := by linarith
  have hf1' : 0 < 1 - f' := by rw [e1]; positivity
  have hcT : c + t' = c + ts - ε := by rw [ht']; ring
  refine ⟨by rw [ht']; linarith, ?_, by linarith, ?_, ?_⟩
  · have : f' - fs = ε * (1 - fs) / (c + ts) := by rw [hf']; field_simp; ring
    have : 0 < f' - fs := by rw [this]; positivity
    linarith
  · unfold vT
    rw [hcT, e1]; field_simp
  · ext v
    simp only [mp, Set.mem_setOf_eq]
    rw [hcT]
    have : v * (1 - f') = v * (1 - fs) * (c + ts - ε) / (c + ts) := by rw [e1]; ring
    rw [this, le_div_iff₀ hpos]
    constructor <;> intro h
    · nlinarith [mul_pos h1 hc', mul_pos hc' hpos]
    · nlinarith [mul_pos h1 hc', mul_pos hc' hpos]
