-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:30.05687+00:00
-- url     : https://prove2.me/submissions/efaf309d-809f-493c-a49c-5b880788d17d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_mul_140b383ad26d
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
theorem _root_.solution (φ : F' →ₗ[F] F) {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F'}
    (hf : f ∈ I.map (map (algebraMap F F'))) : coeffForm φ f ∈ I := by
  have hf' : f ∈ Submodule.span (MvPolynomial σ F')
      ((map (algebraMap F F')) '' (I : Set (MvPolynomial σ F))) := hf
  have key : ∀ c : MvPolynomial σ F', coeffForm φ (c * f) ∈ I := by
    refine Submodule.span_induction (p := fun x _ => ∀ c, coeffForm φ (c * x) ∈ I)
      ?_ ?_ ?_ ?_ hf'
    · rintro _ ⟨g, hg, rfl⟩ c
      rw [mul_comm, coeffForm_map_mul]
      exact I.mul_mem_right _ hg
    · intro c
      simp
    · intro x y _ _ hx hy c
      rw [mul_add, map_add]
      exact I.add_mem (hx c) (hy c)
    · intro a x _ hx c
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (c * a)
  simpa using key 1
end GroundTheory.Heights₂.Heights.FieldNumbers
