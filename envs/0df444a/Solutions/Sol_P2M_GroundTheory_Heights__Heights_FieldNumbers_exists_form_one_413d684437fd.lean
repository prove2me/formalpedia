-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_one_413d684437fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:46.174366+00:00
-- url     : https://prove2.me/submissions/3566942b-2afb-4caa-9b02-08c7a22eb1a7

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
theorem _root_.solution : ∃ φ : F' →ₗ[F] F, φ 1 = 1 := by
  have h : ¬ ∀ φ : Module.Dual F F', φ 1 = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact one_ne_zero
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨(φ 1)⁻¹ • φ, by simp [hφ]⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
