-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.contDiff_fderiv1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:42.949652+00:00
-- url     : https://prove2.me/submissions/62c15487-546a-4182-be5f-806cdabef609

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
theorem _root_.solution : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
end ReciprocityTheory.AnForm.A.GreenFunction
