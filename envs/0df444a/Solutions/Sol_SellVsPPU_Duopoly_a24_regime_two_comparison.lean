-- Prove2me | solution 1 for SellVsPPU.Duopoly.a24_regime_two_comparison
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:12:30.143914+00:00
-- url     : https://prove2.me/submissions/5583185c-af93-48ec-8431-c4a783b4045b

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model
namespace SellVsPPU.Duopoly

/-- The sign comparison is stronger than the printed iso-profit equality calculation. -/
theorem _root_.solution (P : Params) (hP : P.Admissible)
    (hregime : P.qm * (P.a / 2 - P.delta) < P.c) :
    (profSStar P = profUStar P ↔
      2 * P.a * P.qm * (P.a * P.qm - P.c) ^ 2 =
        (P.qm * (P.a - P.delta) - P.c) * (P.a * P.qm + P.c) ^ 2) ∧
    (profSStar P ≤ profUStar P ↔
      P.delta ≤ P.a - P.c / P.qm -
        2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2) := by
  obtain ⟨ha, hq, hc, hd, -⟩ := hP
  have hn : ¬ P.c ≤ P.qm * (P.a / 2 - P.delta) := not_le.2 hregime
  have hS : profSStar P = (2 * P.a * P.qm * (P.a * P.qm - P.c) ^ 2) / (8 * P.qm ^ 2 * P.a ^ 2) := by
    unfold profSStar; rw [if_neg hn]; field_simp; ring
  have hU : profUStar P = ((P.qm * (P.a - P.delta) - P.c) * (P.a * P.qm + P.c) ^ 2) / (8 * P.qm ^ 2 * P.a ^ 2) := by
    unfold profUStar; rw [if_neg hn]
  have hD : 0 < 8 * P.qm ^ 2 * P.a ^ 2 := by positivity
  rw [hS, hU]
  refine ⟨div_left_inj' hD.ne', ?_⟩
  rw [div_le_div_iff_of_pos_right hD]
  have hs : 0 < P.a * P.qm + P.c := by positivity
  have key : (P.qm * (P.a - P.delta) - P.c) * (P.a * P.qm + P.c) ^ 2 - 2 * P.a * P.qm * (P.a * P.qm - P.c) ^ 2
      = (P.qm * (P.a * P.qm + P.c) ^ 2) * ((P.a - P.c / P.qm - 2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2) - P.delta) := by
    field_simp; ring
  have hk : 0 < P.qm * (P.a * P.qm + P.c) ^ 2 := by positivity
  constructor
  · intro h
    have : 0 ≤ (P.qm * (P.a * P.qm + P.c) ^ 2) * ((P.a - P.c / P.qm - 2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2) - P.delta) := by
      rw [← key]; linarith
    have := (mul_nonneg_iff_of_pos_left hk).1 this
    linarith
  · intro h
    have := mul_nonneg hk.le (sub_nonneg.2 h)
    rw [← key] at this
    linarith


end SellVsPPU.Duopoly

