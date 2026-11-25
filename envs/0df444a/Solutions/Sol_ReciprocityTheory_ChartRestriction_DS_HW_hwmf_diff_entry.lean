-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_diff_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:31.47926+00:00
-- url     : https://prove2.me/submissions/8750d48e-1b34-4728-8ff6-b38c3339f144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (i j : Fin n) : Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => x i j) := by
  first
    | exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i) :
        (Fin n → Fin n → ℂ) →L[ℂ] ℂ).differentiable
    | fun_prop
    | exact (differentiable_apply j).comp (differentiable_apply i)
end ReciprocityTheory.ChartRestriction.DS.HW
