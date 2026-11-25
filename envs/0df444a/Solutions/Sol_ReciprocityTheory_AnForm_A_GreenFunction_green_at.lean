-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.green_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:45.034818+00:00
-- url     : https://prove2.me/submissions/8cfd6bf4-729c-4960-841e-a4e349f4e195

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_ee
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_norm_ee
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_polar_symm_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_of_contDiff_two
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_decomp
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_vanish
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_norm_rad
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integral_Arad
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integral_Bang_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integrableOn_log_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_lap
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_lap_vanish
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integrable_log_norm_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z - a‖ * Δ u z = 2 * Real.pi * u a := by
  have hpi := Real.pi_pos
  have hD1 := continuous_fderiv_of_contDiff_two hu
  have hD2 := continuous_fderiv_fderiv hu
  have he := continuous_ee
  have hL := continuous_lap hu
  constructor
  · obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hL.continuousOn
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC a (Metric.mem_closedBall_self hR0.le))
    have hg : Integrable (fun z : ℂ => C * (Iic R).indicator (fun t => ‖Real.log t‖) ‖z - a‖) :=
      ((integrable_log_norm_ball hR0).comp_sub_right a).const_mul C
    refine hg.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub_const a))).mul
        hL.measurable).aestronglyMeasurable
    · rcases le_or_gt ‖z - a‖ R with h | h
      · rw [indicator_of_mem (show ‖z - a‖ ∈ Iic R from h), norm_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left
          (hC z (by rwa [Metric.mem_closedBall, dist_eq_norm])) (norm_nonneg _)
      · rw [lap_vanish hR h, mul_zero, norm_zero]
        exact mul_nonneg hC0 (indicator_nonneg (fun _ _ => norm_nonneg _) _)
  · have ht := integral_add_left_eq_self (μ := volume) (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) a
    simp only [add_sub_cancel_left] at ht
    rw [← ht]
    rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    have htarget : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
      measurableSet_Ioi.prod measurableSet_Ioo
    rw [setIntegral_congr_fun htarget
      (g := fun p : ℝ × ℝ => Arad u a p.2 p.1 + AngularPart u a p.1 p.2) (fun p hp => by
        simp only [polar_symm_eq, smul_eq_mul]
        rw [norm_smul, norm_ee, mul_one, Real.norm_eq_abs, abs_of_pos hp.1, ← decomp]; ring)]
    have hA : IntegrableOn (fun p : ℝ × ℝ => Arad u a p.2 p.1) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) :=
      integrableOn_log_mul (P := fun p : ℝ × ℝ =>
        p.1 * fderiv ℝ (fderiv ℝ u) (a + p.1 • ee p.2) (ee p.2) (ee p.2)
          + fderiv ℝ u (a + p.1 • ee p.2) (ee p.2)) (by fun_prop) hR0 (fun p hp => by
        obtain ⟨h1, h2⟩ := vanish hR (z := a + p.1 • ee p.2)
          (by rw [norm_rad a (by linarith) p.2]; exact hp)
        simp only [h1, h2, ContinuousLinearMap.zero_apply, mul_zero, add_zero])
    have hB : IntegrableOn (fun p : ℝ × ℝ => AngularPart u a p.1 p.2) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) :=
      integrableOn_log_mul (P := fun p : ℝ × ℝ =>
        p.1 * fderiv ℝ (fderiv ℝ u) (a + p.1 • ee p.2) (Complex.I * ee p.2) (Complex.I * ee p.2)
          - fderiv ℝ u (a + p.1 • ee p.2) (ee p.2)) (by fun_prop) hR0 (fun p hp => by
        obtain ⟨h1, h2⟩ := vanish hR (z := a + p.1 • ee p.2)
          (by rw [norm_rad a (by linarith) p.2]; exact hp)
        simp only [h1, h2, ContinuousLinearMap.zero_apply, mul_zero, sub_zero])
    rw [integral_add hA hB]
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hA hB
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hA,
      integral_prod _ hB]
    have eA : ∀ θ : ℝ, ∫ r in Ioi 0, Arad u a θ r = u a := integral_Arad hu a hR0 hR
    have eB : ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, AngularPart u a r θ = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => integral_Bang_eq_zero hu a hr)]
      simp
    simp only [eA, eB, add_zero, setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
end ReciprocityTheory.AnForm.A.GreenFunction
