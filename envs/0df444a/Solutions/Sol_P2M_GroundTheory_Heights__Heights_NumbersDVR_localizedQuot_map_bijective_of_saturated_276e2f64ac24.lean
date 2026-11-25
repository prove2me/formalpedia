-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_map_bijective_of_saturated_276e2f64ac24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:57.65286+00:00
-- url     : https://prove2.me/submissions/941bcac2-5844-4eb0-8d85-3d29e783bb62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtOfSaturated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de


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
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) :
    Function.Bijective (LocalizedModule.map Q.primeCompl
      (Submodule.mapQ J Q LinearMap.id (fun _ ha => hJQ ha) : (A ⧸ J) →ₗ[A] A ⧸ Q)) := by
  refine ⟨?_, LocalizedModule.map_surjective _ _ ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hx
    have haQ : a ∈ Q := localizedQuotient_mk_eq_zero Q a s hx
    obtain ⟨t, ht, hta⟩ := hsat a haQ
    rw [Submodule.mem_bot, ← LocalizedModule.zero_mk (1 : Q.primeCompl), LocalizedModule.mk_eq]
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hta
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
