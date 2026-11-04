-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeBounds.source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:45:57.360743+00:00
-- url     : https://prove2.me/submissions/7f10b231-3c11-49c3-bc3b-1d21ebbcc99d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_zero_native
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeBounds
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory WeightedGlobalLocalParameters
open WeightedGlobalActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredRuntimeBounds
theorem _root_.solution (P : Profile κ) (I : Input) (A : Inputs) (n j seed : ℕ)
    (D : Data (config P.p j I A seed))
    (hj : j≤rounds P n) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(J P n)) (hw : I.weightCap≤weight P n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput (sourceInput I A seed D))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  exact zero_native P (sourceInput I A seed D) n j hj hB hC hO hw
end ThreeSum.WeightedGlobalColoredRuntimeBounds
