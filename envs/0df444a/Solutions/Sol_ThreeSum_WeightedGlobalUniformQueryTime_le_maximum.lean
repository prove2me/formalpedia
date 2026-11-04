-- Prove2me | solution 1 for ThreeSum.WeightedGlobalUniformQueryTime.le_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:13:14.445674+00:00
-- url     : https://prove2.me/submissions/c9164cd7-735f-434a-8eb7-043869468b01

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalUniformQueryTime
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    {j R : ℕ} (hj : j≤R) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j) I (valueCap (r:=j) maps cap I)≤
      maximum maps cap I R :=
  Finset.le_sup (f:=fun j => WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j) I
    (valueCap (r:=j) maps cap I)) (Finset.mem_range.mpr (by omega))
end ThreeSum.WeightedGlobalUniformQueryTime
