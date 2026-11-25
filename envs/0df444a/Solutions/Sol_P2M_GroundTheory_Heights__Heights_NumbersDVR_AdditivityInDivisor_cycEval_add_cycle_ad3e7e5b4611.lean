-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_cycle_ad3e7e5b4611
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:59.007652+00:00
-- url     : https://prove2.me/submissions/fcddad25-b5be-4a17-8fcf-3c8f8ae7c138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe

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
open GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
theorem _root_.solution {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) : cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by
  unfold cycEval
  rw [← finsum_add_distrib (h₁.subset (Function.support_mul_subset_left _ _))
    (h₂.subset (Function.support_mul_subset_left _ _))]
  exact finsum_congr fun W => by simp [add_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
