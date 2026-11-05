-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation.selector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:38:36.163894+00:00
-- url     : https://prove2.me/submissions/289a2137-8227-4847-916d-00ed943b04f5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectorAllocation_word_envelope
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectorAllocation_controls
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaAllocationResources_ok
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceControls_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceValues_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_controls


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
theorem _root_.solution {lim : Limits} {depth : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (n U j nO free : ℕ) (hj : j≤Nat.clog M (n^2))
    (hO : nO≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim free depth) :
    (LightTernaryRowSelector.word
      ((p^(LightWeightedGlobalDimensions.dim M b p K n U))^2)
      ((numbers maps τ cap M b K H drift scale n U j).candidateScore)
      (p^j) (p^j) ((p^(2*K))^j)
      (9^j*n^2) (9^j*n^2)
      ((drift*scale)^j*LightTernaryInitialBudgets.initial K b n
        (LightWeightedGlobalDimensions.J M b n U) nO) : ℤ)≤lim.word := by
  obtain ⟨hT,hd,hp,ht,hinit,hscore,hmenu⟩ := controls maps τ cap M b K H drift scale n U j nO hO
  have hh := word_envelope hT hmenu hscore hd hd hp ht ht hinit
  have he := Alloc.bound n U j hj
  have hc : LightTernaryRowSelector.word
      ((p^(LightWeightedGlobalDimensions.dim M b p K n U))^2)
      ((numbers maps τ cap M b K H drift scale n U j).candidateScore)
      (p^j) (p^j) ((p^(2*K))^j) (9^j*n^2) (9^j*n^2)
      ((drift*scale)^j*LightTernaryInitialBudgets.initial K b n
        (LightWeightedGlobalDimensions.J M b n U) nO)≤capacity Alloc.D Alloc.E (n+U) :=
    hh.trans he
  exact (Int.ofNat_le.mpr hc).trans (WeightedGlobalArenaAllocationResources.ok Alloc hok).2.1
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
