-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.allocated_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:08:32.465202+00:00
-- url     : https://prove2.me/submissions/27586df3-6a5e-4c0b-af61-a114f68270fa

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepareAllocation_allocated
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_allocated
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectorAllocation_initial_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j nO : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (hj : j+1≤Nat.clog M (n^2))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hscale : 1≤drift*scale)
    (hO : nO≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j (LightWeightedGlobalDimensions.J M b n U) n
        (LightTernaryInitialBudgets.initial K b n (LightWeightedGlobalDimensions.J M b n U) nO)
        (p^(2*K)) drift scale I Q)≤I.capacity := by
  apply allocated maps τ cap M b K H drift scale n U j _ Alloc I Q hj hcap hscale
  exact WeightedGlobalArenaSelectorAllocation.initial_le hO _ _ _
end ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
