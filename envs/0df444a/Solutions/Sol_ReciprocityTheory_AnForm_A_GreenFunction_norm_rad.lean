-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.norm_rad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:00.52461+00:00
-- url     : https://prove2.me/submissions/ae899a25-d2a4-488c-b12c-71e8c7e9c17a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_norm_ee

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
theorem _root_.solution (a : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖a + r • ee θ - a‖ = r := by
  simp [norm_ee, abs_of_nonneg hr]
end ReciprocityTheory.AnForm.A.GreenFunction
