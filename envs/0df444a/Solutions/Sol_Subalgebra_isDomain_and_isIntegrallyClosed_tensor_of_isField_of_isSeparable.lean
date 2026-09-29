-- Prove2me | solution 1 for Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/df298896-9ea4-5d24-9865-e1643748ccfa

import Mathlib
import Theorems.Thm_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable

open scoped TensorProduct

universe u

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000

namespace Subalgebra p2m_export "Subalgebra" "algebraMap_apply isDomain val map toAlgebra" end Subalgebra
p2m_open_scoped "Subalgebra" in

theorem Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable
    {R₀ k₀ F : Type u} [CommRing R₀] [IsDomain R₀] [Field k₀] [Algebra R₀ k₀] [IsFractionRing R₀ k₀]
    [Field F] [Algebra R₀ F] [Algebra k₀ F] [IsScalarTower R₀ k₀ F]
    (A : Subalgebra R₀ F) (hIC : IsIntegrallyClosed A) (hfr : IsFractionRing A F)
    (K : Type u) [Field K] [Algebra R₀ K] [Algebra k₀ K] [IsScalarTower R₀ k₀ K]
    [FiniteDimensional k₀ K] [Algebra.IsSeparable k₀ K] (hF : IsField (F ⊗[k₀] K)) :
    IsDomain (K ⊗[R₀] A) ∧ IsIntegrallyClosed (K ⊗[R₀] A) := by
  classical
  set M : Submonoid A := Algebra.algebraMapSubmonoid A (nonZeroDivisors R₀) with hM
  have hinjRA : Function.Injective (algebraMap R₀ A) := by
    intro a b h
    have h' := congrArg (algebraMap A F) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R₀ k₀ F, IsScalarTower.algebraMap_apply R₀ k₀ F] at h'
    exact IsFractionRing.injective R₀ k₀ ((algebraMap k₀ F).injective h')
  have hMle : M ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinjRA).mpr (nonZeroDivisors.ne_zero hr))

  haveI hloc0 : IsLocalization M (A ⊗[R₀] k₀) := IsLocalization.tensor k₀ (nonZeroDivisors R₀)
  letI : Algebra A (k₀ ⊗[R₀] A) := Algebra.TensorProduct.rightAlgebra
  let ecomm : (A ⊗[R₀] k₀) ≃ₐ[A] (k₀ ⊗[R₀] A) :=
    { (Algebra.TensorProduct.comm R₀ A k₀ : A ⊗[R₀] k₀ ≃+* k₀ ⊗[R₀] A) with
      commutes' := fun a => by
        show Algebra.TensorProduct.comm R₀ A k₀ (a ⊗ₜ 1) = 1 ⊗ₜ a
        simp only [Algebra.TensorProduct.comm_tmul] }
  haveI hloc : IsLocalization M (k₀ ⊗[R₀] A) :=
    IsLocalization.isLocalization_of_algEquiv (M := M) (S := A ⊗[R₀] k₀) (P := k₀ ⊗[R₀] A) ecomm
  haveI : IsDomain (k₀ ⊗[R₀] A) := IsLocalization.isDomain_of_le_nonZeroDivisors (k₀ ⊗[R₀] A) hMle
  haveI : IsIntegrallyClosed A := hIC
  haveI : IsIntegrallyClosed (k₀ ⊗[R₀] A) := isIntegrallyClosed_of_isLocalization _ M hMle

  let φ : k₀ ⊗[R₀] A →ₐ[R₀] F :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R₀ k₀ F) A.val
  letI : Algebra (k₀ ⊗[R₀] A) F := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap (k₀ ⊗[R₀] A) F x = φ x := fun _ => rfl
  have hφA : ∀ a : A, φ (algebraMap A (k₀ ⊗[R₀] A) a) = (a : F) := fun a => by
    show φ ((1 : k₀) ⊗ₜ a) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl
  have hφk : ∀ c : k₀, φ (algebraMap k₀ (k₀ ⊗[R₀] A) c) = algebraMap k₀ F c := fun c => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  haveI : IsScalarTower A (k₀ ⊗[R₀] A) F :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := k₀ ⊗[R₀] A) (A := F) fun a => (hφA a).symm
  haveI : IsScalarTower k₀ (k₀ ⊗[R₀] A) F :=
    IsScalarTower.of_algebraMap_eq (R := k₀) (S := k₀ ⊗[R₀] A) (A := F) fun c => (hφk c).symm
  haveI : IsFractionRing A F := hfr
  haveI : IsFractionRing (k₀ ⊗[R₀] A) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M (k₀ ⊗[R₀] A) F

  have h := Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable
    (k₀ := k₀) (S := k₀ ⊗[R₀] A) (F := F) (L := K) hF
  haveI := h.1
  haveI := h.2
  let e := Algebra.TensorProduct.cancelBaseChange R₀ k₀ k₀ K A
  exact ⟨Function.Injective.isDomain (e.symm : K ⊗[R₀] A →+* K ⊗[k₀] (k₀ ⊗[R₀] A)) e.symm.injective,
    IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

theorem solution
    {R₀ k₀ F : Type u} [CommRing R₀] [IsDomain R₀] [Field k₀] [Algebra R₀ k₀] [IsFractionRing R₀ k₀]
    [Field F] [Algebra R₀ F] [Algebra k₀ F] [IsScalarTower R₀ k₀ F]
    (A : Subalgebra R₀ F) (hIC : IsIntegrallyClosed A) (hfr : IsFractionRing A F)
    (K : Type u) [Field K] [Algebra R₀ K] [Algebra k₀ K] [IsScalarTower R₀ k₀ K]
    [FiniteDimensional k₀ K] [Algebra.IsSeparable k₀ K] (hF : IsField (F ⊗[k₀] K)) :
    IsDomain (K ⊗[R₀] A) ∧ IsIntegrallyClosed (K ⊗[R₀] A) :=
  Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable A hIC hfr K hF

end S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable
end P2MW
export P2MW.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isField_of_isSeparable (solution)
