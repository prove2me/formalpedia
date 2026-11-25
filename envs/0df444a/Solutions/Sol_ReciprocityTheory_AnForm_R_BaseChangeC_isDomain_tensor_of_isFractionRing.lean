-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.isDomain_tensor_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:41.361576+00:00
-- url     : https://prove2.me/submissions/2b21fdcf-e6b5-4009-a15c-2629b694aa7e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_fracTensor_exists_den

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
include ι
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution : IsDomain (F ⊗[ℚ] C) := by
  have h1 : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) :=
    IsFractionRing.injective (MvPolynomial ι ℚ) F
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := C)
      (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F).toLinearMap h1
  let e : MvPolynomial ι ℚ ⊗[ℚ] C ≃+* MvPolynomial ι C :=
    (Algebra.TensorProduct.comm ℚ (MvPolynomial ι ℚ) C).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) ℚ C).toRingEquiv
  haveI hD : IsDomain (MvPolynomial ι ℚ ⊗[ℚ] C) := Function.Injective.isDomain e e.injective
  haveI : Nontrivial (F ⊗[ℚ] C) := hinj.nontrivial
  have hu : ∀ s ∈ nonZeroDivisors (MvPolynomial ι ℚ),
      IsUnit (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) := by
    intro s hs
    have h0 : algebraMap (MvPolynomial ι ℚ) F s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    exact (isUnit_iff_ne_zero.mpr h0).map
      (Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := F) (B := C))
  haveI nzd : NoZeroDivisors (F ⊗[ℚ] C) := by
    constructor
    intro a b hab
    obtain ⟨s₁, hs₁, w₁, e₁⟩ := fracTensor_exists_den ι F C a
    obtain ⟨s₂, hs₂, w₂, e₂⟩ := fracTensor_exists_den ι F C b
    have hw : Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
        (AlgHom.id ℚ C) (w₁ * w₂) = 0 := by
      rw [map_mul, ← e₁, ← e₂]
      calc _ = (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) *
            (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * (a * b) := by ring
        _ = 0 := by rw [hab, mul_zero]
    have hw0 : w₁ * w₂ = 0 := hinj (by rw [hw, map_zero])
    rcases mul_eq_zero.mp hw0 with h | h
    · left
      have h' : (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) * a = 0 := by
        rw [e₁, h, map_zero]
      exact ((hu s₁ hs₁).mul_right_eq_zero).mp h'
    · right
      have h' : (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * b = 0 := by
        rw [e₂, h, map_zero]
      exact ((hu s₂ hs₂).mul_right_eq_zero).mp h'
  exact NoZeroDivisors.to_isDomain _
end ReciprocityTheory.AnForm.R.BaseChangeC
