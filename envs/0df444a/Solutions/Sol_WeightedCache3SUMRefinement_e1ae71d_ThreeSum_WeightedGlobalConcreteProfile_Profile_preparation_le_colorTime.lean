-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile.preparation_le_colorTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:12:12.974122+00:00
-- url     : https://prove2.me/submissions/36212910-0e78-41e5-b884-7288cdbf49e8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileRuntime

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light StageBounds WeightedGlobalLocalParameters WeightedGlobalActualColoredRuntime
open WeightedGlobalActualPrefixRuntime WeightedGlobalOversizeOverhead Filter
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile
theorem _root_.solution (P : Profile κ) (n : ℕ) :
    LightWeightedGlobalColorPreparationProof.time n
      (LightWeightedGlobalDimensions.J P.M P.radix n (n^κ)) (n^κ)+
      LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+10000≤
        P.colorTime n := by
  unfold colorTime WeightedGlobalActualGlobalQueryRuntime.uniformTime WeightedGlobalActualColoredRuntime.uniformTime
  change _≤LightWeightedGlobalColorPreparationProof.time n
    (LightWeightedGlobalDimensions.J P.M P.radix n (n^κ)) (n^κ)+_+_+_+10000+_
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile
