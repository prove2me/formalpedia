-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensL_id_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:38:03.651155+00:00
-- url     : https://prove2.me/submissions/82ba2d99-63ad-45fa-8c58-b54f61b96a05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensOp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensTau_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.HW.tensOp_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.HW.tensTau_coe



set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (m : Matrix ι ι ℂ) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL m (1 : V →L[ℂ] V) x i = ∑ j, m i j • x j := by
  simp [tensL_apply]
end ReciprocityTheory.ChartRestriction.DS.HW
