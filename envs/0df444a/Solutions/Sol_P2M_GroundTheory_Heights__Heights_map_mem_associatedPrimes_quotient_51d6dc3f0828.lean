-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_map_mem_associatedPrimes_quotient_51d6dc3f0828
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:28.271002+00:00
-- url     : https://prove2.me/submissions/a0353cd6-1703-4e67-8e2d-e405aeb619ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRingUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMQuotientUnmixed

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
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by
  obtain ⟨hprime, a, rfl⟩ := (isAssociatedPrime_iff (I := p) (M := B ⧸ I)).1 hp
  have hI : I ≤ Submodule.colon (⊥ : Submodule B (B ⧸ I)) {a} := fun b hb => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  refine ⟨hI, (isAssociatedPrime_iff).2 ⟨?_, a, ?_⟩⟩
  · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  · ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rw [← hbb']
      simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using hb'
    · intro h
      exact ⟨b, by simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using h, rfl⟩
end GroundTheory.Heights₂.Heights
