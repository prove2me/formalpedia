-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryTimeMonotone.query
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:02:01.007434+00:00
-- url     : https://prove2.me/submissions/ed247301-8b28-40f4-b900-aee7481aad1b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_prepared
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaQueryTimeMonotone
theorem _root_.solution {V W : ℕ} (I I' : Input) (hV : V≤W) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I V≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' W := by
  classical
  unfold WeightedGlobalArenaCountReady.queryTime
  apply Finset.sup_le
  intro Q hQ
  exact (prepared I I' hV Q).trans (Finset.le_sup (f:=fun Q =>
    LightWeightedPreparedWanted.time (nearConfig (m:=m) (r:=r) I' false W)
      (nearConfig (m:=m) (r:=r) I' true W) Q) hQ)
end ThreeSum.WeightedGlobalArenaQueryTimeMonotone
