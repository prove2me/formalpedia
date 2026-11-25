-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.fracTensor_exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:54.937936+00:00
-- url     : https://prove2.me/submissions/f0e60645-1735-4fbf-92a3-0ec8c769bec6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable (ι : Type) (F : Type) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial ι ℚ) F]
  [IsScalarTower ℚ (MvPolynomial ι ℚ) F] [IsFractionRing (MvPolynomial ι ℚ) F]
  (C : Type) [Field C] [Algebra ℚ C]
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution (z : F ⊗[ℚ] C) :
    ∃ s ∈ nonZeroDivisors (MvPolynomial ι ℚ), ∃ w : MvPolynomial ι ℚ ⊗[ℚ] C,
      (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) * z =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
          (AlgHom.id ℚ C) w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | tmul a c =>
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial ι ℚ)) a
    refine ⟨(s : MvPolynomial ι ℚ), s.2, x ⊗ₜ[ℚ] c, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, mul_comm, hs]
    rfl
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, w₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, w₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂,
      (s₂ ⊗ₜ[ℚ] (1 : C)) * w₁ + (s₁ ⊗ₜ[ℚ] (1 : C)) * w₂, ?_⟩
    have hΦ : ∀ t : MvPolynomial ι ℚ,
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C)
          (t ⊗ₜ[ℚ] (1 : C)) = algebraMap (MvPolynomial ι ℚ) F t ⊗ₜ[ℚ] (1 : C) := fun t => by
      rw [Algebra.TensorProduct.map_tmul]; rfl
    have hsplit : (algebraMap (MvPolynomial ι ℚ) F s₁ * algebraMap (MvPolynomial ι ℚ) F s₂) ⊗ₜ[ℚ] (1 : C) =
        (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) *
          (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [map_add, map_mul, hΦ]
    rw [← e₁, ← e₂, hsplit]
    ring
end ReciprocityTheory.AnForm.R.BaseChangeC
