-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_polynomial_6eef1ef7fe50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:54:06.564786+00:00
-- url     : https://prove2.me/submissions/efda986f-f18a-43ed-9e78-579aeb3f26b2

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
variable {σ : Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P : Ideal (MvPolynomial σ F)) [P.IsPrime] :
    (P.map (map (algebraMap F (Polynomial F)) : MvPolynomial σ F →+* _)).IsPrime := by
  let e : Polynomial (MvPolynomial σ F) ≃+* MvPolynomial σ (Polynomial F) :=
    ((optionEquivLeft F σ).symm.trans (optionEquivRight F σ)).toRingEquiv
  have he : (e : Polynomial (MvPolynomial σ F) →+* MvPolynomial σ (Polynomial F)).comp
      Polynomial.C = map (algebraMap F (Polynomial F)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, map_C, Polynomial.algebraMap_eq]
      show optionEquivRight F σ ((optionEquivLeft F σ).symm (Polynomial.C (C r))) = _
      rw [(AlgEquiv.symm_apply_eq _).mpr (optionEquivLeft_C F σ r).symm, optionEquivRight_C]
    · intro i
      simp only [RingHom.comp_apply, map_X]
      show optionEquivRight F σ ((optionEquivLeft F σ).symm (Polynomial.C (X i))) = _
      rw [(AlgEquiv.symm_apply_eq _).mpr (optionEquivLeft_X_some F σ i).symm, optionEquivRight_X_some]
  rw [← he, ← Ideal.map_map]
  exact Ideal.map_isPrime_of_equiv e
end GroundTheory.Heights₂.Heights.FieldNumbers
