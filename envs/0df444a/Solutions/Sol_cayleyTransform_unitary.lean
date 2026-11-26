-- Prove2me | solution 1 for cayleyTransform_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:20.831161+00:00
-- url     : https://prove2.me/submissions/9a520b80-b05d-44f2-9d7b-08ee44fdcdd3

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_Cayley_Unitary
import Theorems.Thm_cayleyTransform_apply_plus
import Theorems.Thm_norm_cayleyTransform
import Theorems.Thm_sub_I_surjective_of_isSelfAdjoint

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem cayleyTransform_surjective
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (cayleyTransform A hA) := by
  intro y
  obtain ⟨x, hx⟩ := sub_I_surjective_of_isSelfAdjoint A hA y
  refine ⟨A x + Complex.I • (x : E), ?_⟩
  exact (cayleyTransform_apply_plus A hA x).trans hx
end

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    cayleyTransform A hA ∈ unitary (E →L[ℂ] E) := by
  let f : E →ₗᵢ[ℂ] E := LinearIsometry.mk (cayleyTransform A hA).toLinearMap
    (norm_cayleyTransform A hA)
  let e : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.ofSurjective f (cayleyTransform_surjective A hA)
  let u : unitary (E →L[ℂ] E) := Unitary.linearIsometryEquiv.symm e
  have hueq : (u : E →L[ℂ] E) = cayleyTransform A hA := by
    ext x
    change e x = cayleyTransform A hA x
    change f x = cayleyTransform A hA x
    rfl
  rw [← hueq]
  exact u.property
