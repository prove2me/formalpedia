-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_subring_map_maximal_cases_ed7859abe5d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:44.095984+00:00
-- url     : https://prove2.me/submissions/ebd97abb-9e2e-4f9b-8dff-fc9b6040cb93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpOrderLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by
  by_cases h : m ≤ (IsLocalRing.maximalIdeal D).comap C.subtype
  · right
    rw [hm.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal D).ne_top) h]
    exact hC
  · left
    obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp h
    have hu : IsUnit (C.subtype c) := by
      by_contra hnu
      exact hc (IsLocalRing.mem_maximalIdeal _ |>.mpr hnu)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hcm) hu
end GroundTheory.Heights₂.Heights.NumbersDVR
