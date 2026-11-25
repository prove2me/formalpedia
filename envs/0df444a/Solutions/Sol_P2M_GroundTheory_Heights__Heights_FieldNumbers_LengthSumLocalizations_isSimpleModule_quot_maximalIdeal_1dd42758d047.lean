-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isSimpleModule_quot_maximalIdeal_1dd42758d047
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:48.44401+00:00
-- url     : https://prove2.me/submissions/1d7b0c0d-c2c7-4c91-8ac8-8503c6186475

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_algebraMap_quot_maximalIdeal_surjective_b29c85621e4c

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
theorem _root_.solution (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    IsSimpleModule B (C ⧸ IsLocalRing.maximalIdeal C) := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  let : Field (C ⧸ IsLocalRing.maximalIdeal C) := Ideal.Quotient.field _
  rw [← Module.length_eq_one_iff,
    Module.length_eq_of_surjective (algebraMap_quot_maximalIdeal_surjective 𝔪 C)]
  exact Module.length_eq_one _ _
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
