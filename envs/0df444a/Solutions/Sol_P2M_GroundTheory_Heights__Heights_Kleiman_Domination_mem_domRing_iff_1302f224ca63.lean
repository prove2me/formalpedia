-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:36.507178+00:00
-- url     : https://prove2.me/submissions/8a50a06a-8851-48c8-b01f-a86f976264f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_ampleChart_single_iff_f5349f989973

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution (b : Ω) : b ∈ domRing S x x' i ↔
    ∀ J : Chart x', b ∈ chartRing (chartRing S x (singleChart hi)) x' J := by
  rw [domRing, ampleRing, Set.mem_iInter]
  constructor
  · intro hb J
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : x' j ≠ 0 := (mem_support x').mp (J.2.2 hjJ)
    have h1 := (mem_ampleChart_single_iff hi hj b).mp (hb (singleChart hj))
    exact chartRing_mono (Finset.singleton_subset_iff.mpr hjJ) h1
  · intro hb J
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : x' j ≠ 0 := (mem_support x').mp (J.2.2 hjJ)
    have h1 := (mem_ampleChart_single_iff hi hj b).mpr (hb (singleChart hj))
    rw [mem_ampleChart_iff] at h1 ⊢
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, ((pullSys (S := S) x x').pow n).mono _ _ (Finset.singleton_subset_iff.mpr hjJ) _ hn⟩
end GroundTheory.Heights₂.Heights.Kleiman.Domination
