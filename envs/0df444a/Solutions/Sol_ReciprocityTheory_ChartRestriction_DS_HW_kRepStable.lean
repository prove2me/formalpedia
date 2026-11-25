-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.kRepStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:33.980444+00:00
-- url     : https://prove2.me/submissions/afb89086-ac4d-42f9-9eb8-ae16f41760f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_d__stable_of_stable_450b929b4aba
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_stable_of_d__stable_939501e86c53
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__stable_of_stable_ffd49588c4b2


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
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution : KRepStableStatement := by
  intro n ε R W
  constructor
  · intro h a b hab x hx
    exact R.dτ_stable_of_stable W h a b hab x hx
  · intro h
    exact R.stable_of_dτ_stable W (fun a b hab x hx => h a b hab x hx)
end ReciprocityTheory.ChartRestriction.DS.HW
