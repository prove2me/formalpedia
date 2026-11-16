-- Prove2me | solution 1 for QnAudit.smallLogBound_derivative
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:58:05.749217+00:00
-- url     : https://prove2.me/submissions/559107a8-2545-4142-b9e3-38e198a59c26

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (k c t : ℝ) (ht : 0 < t) :
    HasDerivAt (smallLogBound k c)
      (k / t ^ 2 + c + 1/4 - 1/t -
        2 / (t * (2*t^2+1) * Real.log (2+1/t^2))) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have harg : 0 < 2 + 1 / t ^ 2 := by positivity
  have hlog : 0 < Real.log (2 + 1 / t ^ 2) :=
    Real.log_pos (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg t)])
  have hinner := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
  have hargD := hinner.const_add 2
  have hlogD := hargD.log (ne_of_gt harg)
  have hloglogD := hlogD.log (ne_of_gt hlog)
  have hfirst := (hasDerivAt_const t (-k)).div (hasDerivAt_id t) ht0
  have hlinear := (hasDerivAt_id t).const_mul (c + 1/4)
  have h := ((hfirst.add hlinear).sub (Real.hasDerivAt_log ht0)).add hloglogD
  have h' : HasDerivAt (smallLogBound k c)
      ((0*t - -k*1)/t^2 + (c+1/4)*1 - t⁻¹ + (0*t^2 - 1*((2:ℝ)*t^(2-1)*1))/(t^2)^2 / (2+1/t^2) / Real.log (2+1/t^2)) t := h
  have heq : ((0*t - -k*1)/t^2 + (c+1/4)*1 - t⁻¹ + (0*t^2 - 1*((2:ℝ)*t^(2-1)*1))/(t^2)^2 / (2+1/t^2) / Real.log (2+1/t^2)) =
      k / t ^ 2 + c + 1/4 - 1/t -
        2 / (t * (2*t^2+1) * Real.log (2+1/t^2)) := by
    have hfac : 2*t^2+1 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 2*t^2+1)
    field_simp [ht0, ne_of_gt hlog, ne_of_gt harg, hfac]
    <;> ring
  rw [heq] at h'
  exact h'
