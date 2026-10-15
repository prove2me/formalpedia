-- Prove2me | solution 1 for TwoSidedPD.Baseline.lambda_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:51:40.664793+00:00
-- url     : https://prove2.me/submissions/51c3b9b6-ca96-49df-8146-805c77c608ca

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting
open TwoSidedPD.Baseline

theorem solution(v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    0 < lam b θH θL := by
  unfold Assumption1 at hA
  obtain ⟨⟨hv0, hv⟩, hbt⟩ := hA
  unfold lam
  nlinarith [mul_pos hb hL, mul_pos hb (sub_pos.2 hLH), mul_pos hL (sub_pos.2 hLH), sq_nonneg (θH - θL), sq_nonneg (b + θL), sq_nonneg (b + θH), mul_pos (mul_pos hb hL) hL, mul_pos hv0 hb]
