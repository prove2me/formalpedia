-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.allocated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:54:12.766241+00:00
-- url     : https://prove2.me/submissions/54b58914-0393-48e4-b264-4e62abe50dd6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepareAllocation_envelope_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_total_le
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Numbers_sum_list
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_total_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j U0 : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (hj : j+1≤Nat.clog M (n^2))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hscale : 1≤drift*scale)
    (hU0 : U0≤LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightWeightedGlobalDimensions.J M b n U) (n*2^(LightWeightedGlobalDimensions.J M b n U))) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j (LightWeightedGlobalDimensions.J M b n U) n U0
        (p^(2*K)) drift scale I Q)≤I.capacity := by
  have hb := envelope_bound maps τ cap M b K H drift scale n U j U0 I Q hscale hU0
  have hs : (numbers maps τ cap M b K H drift scale n U (j+1)).prefixCells+
      (numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader≤
      total maps τ cap M b K H drift scale n U (j+1) := by
    unfold total
    generalize numbers maps τ cap M b K H drift scale n U (j+1)=A
    rw [Numbers.sum_list]
    omega
  rw [hcap]
  exact hb.trans (hs.trans (Alloc.total_le n U (j+1) hj))
end ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
