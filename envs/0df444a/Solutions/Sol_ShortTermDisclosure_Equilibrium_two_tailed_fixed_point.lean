-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.two_tailed_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:51:46.138845+00:00
-- url     : https://prove2.me/submissions/1ee67325-21aa-4ffb-b20d-04d3c436a265

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

open ShortTermDisclosure.Equilibrium in
theorem solution (P : Params) (hP : P.Standing)
    (v1 v2 : ℝ) (hlo : P.vlo ≤ v1) (h12 : v1 < v2) (hhi : v2 ≤ P.vhi) :
    (belief P (Set.Ioo v1 v2) = v2 ↔
      P.p / (1 - P.p) * (v2 - v1) ^ 2 =
        2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - v2)) ∧
    (belief P (Set.Ioo v1 v2) = v2 → v2 < (P.vhi + P.vlo) / 2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have hint : (∫ v in Set.Ioo v1 v2, v) = (v2 ^ 2 - v1 ^ 2) / 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h12.le,
      integral_id]
  have hvol : (MeasureTheory.volume (Set.Ioo v1 v2)).toReal = v2 - v1 := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  have hL : 0 < P.vhi - P.vlo := by linarith
  have hq : 0 < 1 - P.p := by linarith
  have hden : 0 < P.p * ((v2 - v1) / (P.vhi - P.vlo)) + (1 - P.p) := by
    have : 0 ≤ P.p * ((v2 - v1) / (P.vhi - P.vlo)) :=
      mul_nonneg h4.le (div_nonneg (by linarith) hL.le)
    linarith
  have key : belief P (Set.Ioo v1 v2) = v2 ↔
      P.p / (1 - P.p) * (v2 - v1) ^ 2 =
        2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - v2) := by
    unfold belief
    simp only
    rw [hint, hvol, div_eq_iff hden.ne']
    constructor
    · intro h
      rw [div_mul_eq_mul_div, div_eq_iff hq.ne']
      field_simp at h
      first | linarith | nlinarith [h]
    · intro h
      rw [div_mul_eq_mul_div, div_eq_iff hq.ne'] at h
      field_simp
      first | linarith | nlinarith [h]
  refine ⟨key, fun h => ?_⟩
  have e := key.mp h
  have hpos : 0 < P.p / (1 - P.p) * (v2 - v1) ^ 2 :=
    mul_pos (div_pos h4 hq) (pow_pos (by linarith) 2)
  rw [e] at hpos
  by_contra hc
  push_neg at hc
  nlinarith
