-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_algebraMap_quot_maximalIdeal_surjective_b29c85621e4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:33.607994+00:00
-- url     : https://prove2.me/submissions/9db9fb47-311b-4ce0-8cfa-bdaa51424531

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Module TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
variable {B : Type*} [CommRing B]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
theorem _root_.solution (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*)
    [CommRing C] [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    Function.Surjective (algebraMap B (C ⧸ IsLocalRing.maximalIdeal C)) := by
  intro _ y
  obtain ⟨x, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 C).surjective y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨b, by rw [← hx]; rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
