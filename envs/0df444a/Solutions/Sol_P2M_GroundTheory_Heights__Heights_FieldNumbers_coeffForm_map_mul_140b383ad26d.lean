-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_mul_140b383ad26d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:14.481801+00:00
-- url     : https://prove2.me/submissions/57fb6147-7f72-4908-b624-4252bf89b98a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_form_algebraMap_mul_519b69638a62
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
theorem _root_.solution (φ : F' →ₗ[F] F) (g : MvPolynomial σ F) (f : MvPolynomial σ F') :
    coeffForm φ (map (algebraMap F F') g * f) = g * coeffForm φ f := by
  classical
  ext ν
  simp only [coeff_coeffForm, coeff_mul, map_sum, coeff_map, form_algebraMap_mul]
end GroundTheory.Heights₂.Heights.FieldNumbers
