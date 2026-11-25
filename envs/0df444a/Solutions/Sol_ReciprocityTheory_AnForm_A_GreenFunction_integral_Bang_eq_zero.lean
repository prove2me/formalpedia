-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.integral_Bang_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:37.341527+00:00
-- url     : https://prove2.me/submissions/1e8ba7a3-5dcb-437d-a4f3-02e747cb80c7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_ee
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_ee_pi
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_of_contDiff_two
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang__c26e57c11cae

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
theorem _root_.solution {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-Real.pi) Real.pi, AngularPart u a r θ = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hB : ∀ θ, AngularPart u a r θ = (Real.log r / r) *
      (fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (r • (Complex.I * ee θ)) (r • (Complex.I * ee θ))
        - r * fderiv ℝ u (a + r • ee θ) (ee θ)) := by
    intro θ
    simp only [AngularPart, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    field_simp
  simp_rw [hB]
  have hD1 := continuous_fderiv_of_contDiff_two hu
  have hD2 := continuous_fderiv_fderiv hu
  have he := continuous_ee
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hasDerivAt_ang' hu a r θ)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [ee_pi]; simp
end ReciprocityTheory.AnForm.A.GreenFunction
