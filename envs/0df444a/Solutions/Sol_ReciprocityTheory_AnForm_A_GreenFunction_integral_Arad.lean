-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.integral_Arad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:34.48454+00:00
-- url     : https://prove2.me/submissions/7d301519-deba-4482-908c-1c3a7b229ff2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_ee
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_of_contDiff_two
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad__ec5f7a31e028
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_vanish
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_norm_rad

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
    (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) (θ : ℝ) :
    ∫ r in Ioi 0, Arad u a θ r = u a := by
  have hz : ∀ r, R < r → Arad u a θ r = 0 := fun r hr => by
    obtain ⟨h1, h2⟩ := vanish hR (z := a + r • ee θ) (by rw [norm_rad a (by linarith) θ]; exact hr)
    simp only [Arad, h1, h2, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0:ℝ) (R + 1) ⊆ Ioi 0)
    (fun r hr => hz r (by
      simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hr; linarith [hr.2 hr.1]))]
  rw [← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ R + 1)]
  have hD1 := continuous_fderiv_of_contDiff_two hu
  have hD2 := continuous_fderiv_fderiv hu
  have he := continuous_ee
  have hF : ∀ r ∈ Ioo (0:ℝ) (R + 1), HasDerivAt
      (fun r => r * Real.log r * fderiv ℝ u (a + r • ee θ) (ee θ) - u (a + r • ee θ))
      (Arad u a θ r) r := by
    intro r hr
    have := ((Real.hasDerivAt_mul_log hr.1.ne').mul (hasDerivAt_rad' hu a (ee θ) r)).sub
      (hasDerivAt_rad hu a (ee θ) r)
    refine this.congr_deriv ?_
    simp only [Arad]; ring
  have hcont : ContinuousOn
      (fun r : ℝ => r * Real.log r * fderiv ℝ u (a + r • ee θ) (ee θ) - u (a + r • ee θ))
      (Icc 0 (R + 1)) := by
    apply Continuous.continuousOn
    have h0 := hu.continuous
    have hg : Continuous fun r : ℝ => fderiv ℝ u (a + r • ee θ) (ee θ) := by fun_prop
    exact (Real.continuous_mul_log.mul hg).sub (by fun_prop)
  have hint : IntervalIntegrable (Arad u a θ) volume 0 (R + 1) := by
    have hP : Continuous (fun r : ℝ => r * fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (ee θ) (ee θ)
        + fderiv ℝ u (a + r • ee θ) (ee θ)) := by fun_prop
    exact intervalIntegrable_log'.mul_continuousOn hP.continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hF hint]
  obtain ⟨h1, -⟩ := vanish hR (z := a + (R + 1) • ee θ)
    (by rw [norm_rad a (by linarith) θ]; linarith)
  have h0 : u (a + (R + 1) • ee θ) = 0 := hR _ (by rw [norm_rad a (by linarith) θ]; linarith)
  rw [h1, h0]; simp
end ReciprocityTheory.AnForm.A.GreenFunction
