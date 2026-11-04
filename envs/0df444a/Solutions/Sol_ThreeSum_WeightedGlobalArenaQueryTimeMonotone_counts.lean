-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryTimeMonotone.counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:07:20.19264+00:00
-- url     : https://prove2.me/submissions/0e97bb10-fe67-478c-9b7c-b8e135c1ed9d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_query
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_value

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaQueryTimeMonotone
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I)≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I') :=
  query I I' (value maps cap I I' hB hC hw)
end ThreeSum.WeightedGlobalArenaQueryTimeMonotone
