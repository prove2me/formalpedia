-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_GreenFunction_hasDerivAt_rad__ec5f7a31e028
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:24.028517+00:00
-- url     : https://prove2.me/submissions/e037bf8d-e6dc-4cce-8453-6eab1a2c846e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
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
theorem _root_.solution (e : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => fderiv ℝ u (a + r • e) e)
      (fderiv ℝ (fderiv ℝ u) (a + r • e) e e) r := by
  have hp : HasDerivAt (fun r : ℝ => a + r • e) e r := by
    simpa using ((hasDerivAt_id r).smul_const e).const_add a
  have h2 := (((contDiff_fderiv1 hu).differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt r hp
  simpa using h2.clm_apply (hasDerivAt_const r e)
end ReciprocityTheory.AnForm.A.GreenFunction
