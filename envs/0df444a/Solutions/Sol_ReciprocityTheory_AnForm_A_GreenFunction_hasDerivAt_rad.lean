-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.hasDerivAt_rad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:27.45733+00:00
-- url     : https://prove2.me/submissions/a2feb5d2-cde7-4b64-b39d-4784ac1f3270

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar

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
    HasDerivAt (fun r : ℝ => u (a + r • e)) (fderiv ℝ u (a + r • e) e) r := by
  have hp : HasDerivAt (fun r : ℝ => a + r • e) e r := by
    simpa using ((hasDerivAt_id r).smul_const e).const_add a
  exact ((hu.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt r hp
end ReciprocityTheory.AnForm.A.GreenFunction
