-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.highest_weight_fn_mem_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:39.784652+00:00
-- url     : https://prove2.me/submissions/23ceba07-f805-40cd-b599-a9e12edb9e70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rtr_one

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
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m ∈ Vsp ε m := by
  have h : rtr ε 1 (f0K ε m) ∈ Vsp ε m := Submodule.subset_span ⟨1, rfl⟩
  rwa [rtr_one] at h
end ReciprocityTheory.ChartRestriction.DS.HW
