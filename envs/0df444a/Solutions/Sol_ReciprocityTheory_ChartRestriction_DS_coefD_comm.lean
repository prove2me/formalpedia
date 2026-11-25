-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefD_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:09.399203+00:00
-- url     : https://prove2.me/submissions/30f89498-a67c-4f47-bdbd-b7a35f335775

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefPm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_diagOp_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (A : Module.End ℂ M) (B : Matrix (Fin n) (Fin n) ℂ) :
    Commute (coefPm (M := M) B) (diagOp A) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  simp only [Module.End.mul_apply, coefPm_apply, diagOp_coord, map_sum, map_smul]
end ReciprocityTheory.ChartRestriction.DS
