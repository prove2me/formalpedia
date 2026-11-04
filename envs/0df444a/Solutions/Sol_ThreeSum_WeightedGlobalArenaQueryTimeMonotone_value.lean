-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryTimeMonotone.value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:38:10.831893+00:00
-- url     : https://prove2.me/submissions/a6f1806f-2c6f-4cdb-addb-7b6a9160fefe

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaQueryTimeMonotone
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    valueCap (r:=r) maps cap I≤valueCap (r:=r) maps cap I' := by
  unfold valueCap
  gcongr
end ThreeSum.WeightedGlobalArenaQueryTimeMonotone
