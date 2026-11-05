-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime.le_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:40:17.178329+00:00
-- url     : https://prove2.me/submissions/a9c50f53-4aaa-4bd5-ac60-c824d4f88667

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    {j R : ℕ} (hj : j≤R) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j) I (valueCap (r:=j) maps cap I)≤
      maximum maps cap I R :=
  Finset.le_sup (f:=fun j => WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j) I
    (valueCap (r:=j) maps cap I)) (Finset.mem_range.mpr (by omega))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
