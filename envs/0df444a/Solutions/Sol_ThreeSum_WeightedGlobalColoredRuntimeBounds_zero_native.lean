-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeBounds.zero_native
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:28:20.509059+00:00
-- url     : https://prove2.me/submissions/fadab8f6-5d9b-42d9-831b-99f5333b1b38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalUniformQueryTime_allocated_word


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
theorem _root_.solution (P : Profile κ) (I : Input) (n j : ℕ)
    (hj : j≤rounds P n) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(J P n)) (hw : I.weightCap≤weight P n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput I)
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  refine ⟨hB,hC,hO,?_,Nat.zero_le _⟩
  exact WeightedGlobalUniformQueryTime.allocated_word P.maps P.allocation (zeroInput I) hj hB hC hO hw
end ThreeSum.WeightedGlobalColoredRuntimeBounds
