-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_weightedHomogeneousComponent_fab16ab76a0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:18.888285+00:00
-- url     : https://prove2.me/submissions/e8133096-2fae-49cb-8042-a77e287ca8a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.FieldNumbers.coeff_coeffForm

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {M : Type*} [AddCommMonoid M] (φ : F' →ₗ[F] F)
    (w : σ → M) (n : M) (f : MvPolynomial σ F') :
    coeffForm φ (weightedHomogeneousComponent w n f) =
      weightedHomogeneousComponent w n (coeffForm φ f) := by
  classical
  ext ν
  simp only [coeff_coeffForm, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FieldNumbers
