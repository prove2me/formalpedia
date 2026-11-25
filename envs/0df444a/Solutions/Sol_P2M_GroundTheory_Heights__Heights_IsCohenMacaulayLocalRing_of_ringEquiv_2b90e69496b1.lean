-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsCohenMacaulayLocalRing_of_ringEquiv_2b90e69496b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:03.968188+00:00
-- url     : https://prove2.me/submissions/b17cb1ac-de8d-43ad-9a0f-f111949d4d38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMParameterQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace IsCohenMacaulayLocalRing
theorem _root_.solution {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by
  have : Nontrivial C := e.injective.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv A e
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  refine { exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs' := hm s hs
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs' ⊢
    exact fun h => hs' (by simpa using h.map e.symm)
  · have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)
    exact (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]
end IsCohenMacaulayLocalRing
end GroundTheory.Heights₂.Heights
