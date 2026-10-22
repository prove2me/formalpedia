-- Prove2me | solution 1 for RetailerMarketplace.UnitFee.lemma_B_1_sbt_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:29:39.930428+00:00
-- url     : https://prove2.me/submissions/95e8545d-145d-41ce-b502-7b6b037d7044

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

set_option autoImplicit false
open MeasureTheory RetailerMarketplace.UnitFee

theorem solution (c fs ts ε f' t' : ℝ) (hc : 0 < c)
    (hfs : fs ∈ Set.Ico (0 : ℝ) 1) (hε : 0 < ε) (hεts : ε < ts)
    (hf' : f' = (ε + fs * (c + ts - ε)) / (c + ts)) (ht' : t' = ts - ε) (v : ℝ) :
    v * f' + t' > v * fs + ts ↔ vT c fs ts < v := by
  obtain ⟨hf0, hf1⟩ := hfs
  have hpos : 0 < c + ts := by linarith
  have h1 : 0 < 1 - fs := by linarith
  have key : v * f' + t' - (v * fs + ts) = ε * ((1 - fs) * v - (c + ts)) / (c + ts) := by
    rw [hf', ht']; field_simp; ring
  unfold vT
  rw [div_lt_iff₀ h1, gt_iff_lt, ← sub_pos, key, div_pos_iff_of_pos_right hpos]
  constructor <;> intro h
  · have := pos_of_mul_pos_right h hε.le
    nlinarith
  · exact mul_pos hε (by nlinarith)
