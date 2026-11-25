-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_eq_of_mul_mem_d9e599294e02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:01.268799+00:00
-- url     : https://prove2.me/submissions/780b538a-f155-41c5-88c8-27d34a9ad826

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivisorIdealCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89


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
noncomputable section
universe u
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {J J' U : Ideal (MRing ι R)} {s t : MRing ι R} (hs : s ∉ U)
    (ht : t ∉ U) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    idealCycle J U = idealCycle J' U := by
  unfold idealCycle
  by_cases h : U ∈ J.minimalPrimes ∧ IsRelevant U
  · have h' : U ∈ J'.minimalPrimes ∧ IsRelevant U :=
      ⟨mem_minimalPrimes_of_mul_mem hs ht hsJ htJ h.1, h.2⟩
    rw [dif_pos h, dif_pos h']
    have : U.IsPrime := h.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hs ht hsJ htJ]
  · have h' : ¬ (U ∈ J'.minimalPrimes ∧ IsRelevant U) := fun h' =>
      h ⟨mem_minimalPrimes_of_mul_mem ht hs htJ hsJ h'.1, h'.2⟩
    rw [dif_neg h, dif_neg h']
end GroundTheory.Heights₂.Heights.NumbersDVR
