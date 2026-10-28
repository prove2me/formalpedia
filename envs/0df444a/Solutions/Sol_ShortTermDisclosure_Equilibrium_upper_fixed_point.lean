-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.upper_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:50:07.556213+00:00
-- url     : https://prove2.me/submissions/453fdf25-c654-4489-8e3a-0afeda4603de

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

open ShortTermDisclosure.Equilibrium in
theorem solution (P : Params) (hP : P.Standing)
    (vp : ℝ) (hlo : P.vlo < vp) (hhi : vp ≤ P.vhi) :
    belief P (Set.Ico P.vlo vp) = vp ↔
      P.p / (1 - P.p) * (vp - P.vlo) ^ 2 =
        2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - vp) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have hint : (∫ v in Set.Ico P.vlo vp, v) = (vp ^ 2 - P.vlo ^ 2) / 2 := by
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlo.le,
      integral_id]
  have hvol : (MeasureTheory.volume (Set.Ico P.vlo vp)).toReal = vp - P.vlo := by
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  have hL : 0 < P.vhi - P.vlo := by linarith
  have hq : 0 < 1 - P.p := by linarith
  have hden : 0 < P.p * ((vp - P.vlo) / (P.vhi - P.vlo)) + (1 - P.p) := by
    have : 0 ≤ P.p * ((vp - P.vlo) / (P.vhi - P.vlo)) :=
      mul_nonneg h4.le (div_nonneg (by linarith) hL.le)
    linarith
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
