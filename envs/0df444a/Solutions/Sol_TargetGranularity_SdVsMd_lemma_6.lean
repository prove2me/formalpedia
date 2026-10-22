-- Prove2me | solution 1 for TargetGranularity.SdVsMd.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:06:02.074612+00:00
-- url     : https://prove2.me/submissions/ae00bb9f-c59d-4cd4-a7bb-d1b550821f63

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model
set_option autoImplicit false

open TargetGranularity.SdVsMd

theorem solution (p cad : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadp2 : cad < p ^ 2) (hcadp1 : cad < p * (1 - p)) :
    (1 - p) ^ 2 / 2 < cmaxClick cad p ∧ cmaxClick cad p < (1 - p) / 2 := by
  have h1 : ¬ (p * (1 - p) < cad) := not_lt.2 hcadp1.le
  have h2 : cad ≤ p ^ 2 := hcadp2.le
  have hval : cmaxClick cad p = (cad ^ 2 - 3 * cad * (1 - p) * p + 3 * (1 - p) ^ 2 * p ^ 2) /
      (6 * p * (p * (1 - p) * (1 + p) - cad)) := by
    unfold cmaxClick
    rw [if_neg h1, if_pos h2]
  rw [hval]
  have hq : 0 < 1 - p := by linarith
  have hD : 0 < 6 * p * (p * (1 - p) * (1 + p) - cad) := by
    have : 0 < p * (1 - p) * (1 + p) - cad := by nlinarith [mul_pos hp0 hq]
    positivity
  constructor
  · rw [lt_div_iff₀ hD]
    nlinarith [mul_pos hp0 hq, mul_pos hcad hq, mul_pos hcad hp0, mul_pos (mul_pos hp0 hq) hcad,
      sq_nonneg (cad - p * (1 - p)), mul_pos (sub_pos.2 hcadp1) (sub_pos.2 hcadp2),
      mul_pos (sub_pos.2 hcadp1) hp0, mul_pos (sub_pos.2 hcadp2) hq, mul_pos (sub_pos.2 hcadp1) hq]
  · rw [div_lt_iff₀ hD]
    nlinarith [mul_pos hp0 hq, mul_pos hcad hq, mul_pos hcad hp0, mul_pos (mul_pos hp0 hq) hcad,
      sq_nonneg (cad - p * (1 - p)), mul_pos (sub_pos.2 hcadp1) (sub_pos.2 hcadp2),
      mul_pos (sub_pos.2 hcadp1) hp0, mul_pos (sub_pos.2 hcadp2) hq, mul_pos (sub_pos.2 hcadp1) hq]
