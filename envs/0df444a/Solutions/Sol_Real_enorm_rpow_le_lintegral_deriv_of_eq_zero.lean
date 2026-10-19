-- Prove2me | solution 1 for Real.enorm_rpow_le_lintegral_deriv_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:50:37.208262+00:00
-- url     : https://prove2.me/submissions/9efeb1fd-68ac-4bbc-8321-bd71fc1ade76

import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Set
open scoped ENNReal ContDiff
set_option autoImplicit false

theorem solution (r : ℝ) (hr : 1 ≤ r) (g : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hg : ContDiffOn ℝ 1 g (Icc a b)) (hb : g b = 0) :
    ‖g a‖ₑ ^ r ≤ ENNReal.ofReal r *
      ∫⁻ t in Ioo a b, ‖g t‖ₑ ^ (r - 1) * ‖deriv g t‖ₑ := by
  rcases hr.eq_or_lt with rfl | hr
  · simpa [hb] using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hg hab).trans_eq
        (by rw [← restrict_Ioo_eq_restrict_Icc])
  let v : ℝ → ℝ := fun t => ‖g t‖ ^ r
  have hv : ContDiffOn ℝ 1 v (Icc a b) :=
    (contDiff_norm_rpow hr).comp_contDiffOn hg
  have hvb : v b = 0 := by simp [v, hb, (zero_lt_one.trans hr).ne']
  have hbase := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hv hab
  have hleft : ‖v b - v a‖ₑ = ‖g a‖ₑ ^ r := by
    rw [hvb, zero_sub, enorm_neg]
    simpa only [v, enorm_norm] using
      Real.enorm_rpow_of_nonneg (norm_nonneg (g a)) (zero_lt_one.trans hr).le
  rw [hleft, ← restrict_Ioo_eq_restrict_Icc] at hbase
  refine hbase.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hd : DifferentiableAt ℝ g t :=
    ((hg t ⟨ht.1.le, ht.2.le⟩).contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hnorm : ‖deriv v t‖ ≤ r * ‖g t‖ ^ (r - 1) * ‖deriv g t‖ := by
    rw [norm_deriv_eq_norm_fderiv, show v = (fun x : ℝ => ‖x‖ ^ r) ∘ g from rfl,
      fderiv_comp t (differentiable_norm_rpow hr (g t)) hd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (by
      rw [norm_fderiv_norm_id_rpow _ hr, ← norm_deriv_eq_norm_fderiv])
  have hh := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_mul (mul_nonneg (zero_lt_one.trans hr).le (by positivity)),
    ENNReal.ofReal_mul (zero_lt_one.trans hr).le,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (sub_nonneg.mpr hr.le)] at hh
  simpa only [ofReal_norm, mul_assoc] using hh

