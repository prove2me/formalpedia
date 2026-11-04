-- Prove2me | solution 1 for ThreeSum.WeightedGlobalUniformQueryTime.allocated_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:16:41.722653+00:00
-- url     : https://prove2.me/submissions/0105d9a1-6320-4d6c-9537-64d66d37304e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_fits
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_front_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalUniformQueryTime
theorem _root_.solution {τ cap M b K H drift scale n U r : ℕ}
    (maps : Fin F→Weight m p) (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (hr : r≤Nat.clog M (n^2)) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    WeightedGlobalFrontendResources.eulerBound (N m r) (valueCap (r:=r) maps cap I)≤
      (256*(Alloc.D+1))*(n+U+1)^Alloc.E := by
  have hfront := WeightedGlobalArenaFrontBounds.front_bounds (r:=r) maps τ cap M b K H drift scale I n U
    hB hC hO hweight
  have hdivision := hfront.2.2.2.2.2.2.2.1
  have hfits := (Alloc.fits n U r hr).nearDivision
  change _≤WeightedGlobalArenaLayout.capacity Alloc.D Alloc.E (n+U)
  omega
end ThreeSum.WeightedGlobalUniformQueryTime
