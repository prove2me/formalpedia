-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ang__c26e57c11cae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:52.797955+00:00
-- url     : https://prove2.me/submissions/4a130218-8f26-41b4-bb9a-0a0df1178101

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_ee
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_contDiff_fderiv1

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
variable {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ)
include hu
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => fderiv ℝ u (a + r • ee θ) (r • (Complex.I * ee θ)))
      (fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (r • (Complex.I * ee θ)) (r • (Complex.I * ee θ))
        - r * fderiv ℝ u (a + r • ee θ) (ee θ)) θ := by
  have hp : HasDerivAt (fun θ : ℝ => a + r • ee θ) (r • (Complex.I * ee θ)) θ :=
    ((hasDerivAt_ee θ).const_smul r).const_add a
  have hq : HasDerivAt (fun θ : ℝ => r • (Complex.I * ee θ)) (r • (Complex.I * (Complex.I * ee θ))) θ :=
    ((hasDerivAt_ee θ).const_mul Complex.I).const_smul r
  have h2 := (((contDiff_fderiv1 hu).differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ hp
  refine (h2.clm_apply hq).congr_deriv ?_
  rw [← mul_assoc, Complex.I_mul_I]
  simp only [neg_one_mul, smul_neg, map_neg, map_smul, smul_eq_mul, sub_eq_add_neg]
  rfl
end ReciprocityTheory.AnForm.A.GreenFunction
