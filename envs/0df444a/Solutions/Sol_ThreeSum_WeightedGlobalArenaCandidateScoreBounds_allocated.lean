-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaCandidateScoreBounds.allocated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:51:40.083388+00:00
-- url     : https://prove2.me/submissions/cbf081aa-a076-472d-8a6d-d5a3841cbb85

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_common_cap
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocationResources_ok
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_fits
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCandidateScoreBounds
open WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds WeightedGlobalNativeTensorScore
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaCandidateScoreBounds
theorem _root_.solution {lim : Light.Limits} {depth : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Alloc : WeightedGlobalArenaAllocation.Allocation maps τ cap M b K H drift scale)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=WeightedGlobalArenaLayout.capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2))
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,|L i a|≤(tag : ℤ))
    (hR : ∀i<I.nC,∀a<A.J+2,|R i a|≤(tag : ℤ)) :
    |D.collisionB|≤(I.capacity : ℤ) ∧ |D.collisionC|≤(I.capacity : ℤ) ∧
    |(WeightedGlobalArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤(I.capacity : ℤ) ∧
    (I.capacity : ℤ)≤lim.word := by
  have hc := (Alloc.fits n U r hr).candidateScore
  rw [←hcap] at hc
  obtain ⟨hB,hC,hP⟩ := common_cap maps τ cap M b K H drift scale tag Q I A seed n U D L R
    hJ hnB hnC hO htag hL hR
  have hw := (WeightedGlobalArenaAllocationResources.ok Alloc hok).2.1
  rw [←hcap] at hw
  exact ⟨hB.trans (Int.ofNat_le.mpr hc),hC.trans (Int.ofNat_le.mpr hc),
    hP.trans (Int.ofNat_le.mpr hc),hw⟩
end ThreeSum.WeightedGlobalArenaCandidateScoreBounds
