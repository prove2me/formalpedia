-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixCommit.layout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:56:32.426914+00:00
-- url     : https://prove2.me/submissions/8f8ec432-9fa4-44f7-90d3-fe0b8c2c8e77

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_region_space
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
namespace ThreeSum.WeightedGlobalArenaPrefixCommit
theorem _root_.solution (p r rows : ℕ) (I : Input) (A : Inputs) {lim : Limits}
    (h48 : 48≤I.capacity) (hB : I.nB≤I.capacity) (hC : I.nC≤I.capacity)
    (hO : I.requesterCount≤I.capacity) (hSpan : rows*A.J≤I.capacity)
    (hspace : finish I.free I.capacity≤lim.space) :
    Layout (config p r I A 0) lim (addr I.free I.capacity 3) rows (addr I.free I.capacity 8) :=by
  constructor
  · exact before (by decide : 3<4) h48
  · exact before (by decide : 4<5) hB
  · exact before (by decide : 5<6) hC
  · exact before (by decide : 6<16) hO
  · exact before (by decide : 6<17) hO
  · exact before (by decide : 6<18) hO
  · exact region_space (by decide : 16<slots) hB hspace
  · exact region_space (by decide : 17<slots) hC hspace
  · exact region_space (by decide : 18<slots) hO hspace
  · exact before (by decide : 6<7) hO
  · exact before (by decide : 7<8) hSpan
  · exact region_space (by decide : 8<slots) hSpan hspace
end ThreeSum.WeightedGlobalArenaPrefixCommit
