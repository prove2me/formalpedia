-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMQuotientUnmixed_proof_cb9bc8398e8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:23.814377+00:00
-- url     : https://prove2.me/submissions/bf2388a6-1f1b-4398-8e67-ccadc2d3d0ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRingUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMQuotientUnmixed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_mem_associatedPrimes_quotient_51d6dc3f0828

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
namespace CMQuotientUnmixed
theorem _root_.solution (hQ : CMParameterQuotient.Statement) (hU : CMRingUnmixed.Statement) :
    CMQuotientUnmixed.Statement := by
  intro B _ _ d x hx hdim p hp
  set I := Ideal.span (Set.range x) with hIdef
  have hCM : IsCohenMacaulayLocalRing (B ⧸ I) := hQ B d x hx hdim
  obtain ⟨hIp, hq⟩ := map_mem_associatedPrimes_quotient I p hp
  obtain ⟨hmin, hdq⟩ := hU (B ⧸ I) _ hq
  have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hIp]
  refine ⟨?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨_, hmin, hcomap⟩
  · rw [← hdq]
    exact (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)).symm
end CMQuotientUnmixed
end GroundTheory.Heights₂.Heights
