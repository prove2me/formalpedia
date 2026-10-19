-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/dbecc964-9ad4-4222-a989-37e52844c076

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_isScalarTower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    Module.Finite (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) := by
  classical
  let T := homogeneousMapSubalgebra F
  let S := MvPolynomial (Fin k) ℂ
  let P := Polynomial ℂ
  let Q := homogeneousMapAllTargetReesQuotient F target e
  let I : Ideal (MvPolynomial (Fin (k + 1)) ℂ) :=
    Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e))
  let sourceMap : S →+* Q :=
    (Ideal.Quotient.mk I).comp (MvPolynomial.rename Fin.succ).toRingHom
  letI : Algebra T P :=
    (homogeneousMapReesTargetHom
      F e he hF hzero target).toRingHom.toAlgebra
  letI : Algebra P Q := homogeneousMapAllTargetReesParameterAlgebra F target e
  letI : Algebra T Q := homogeneousMapAllTargetReesSourceAlgebra F target e
  letI : Algebra S Q := sourceMap.toAlgebra
  letI : IsScalarTower T P Q :=
    homogeneousMap_allTarget_rees_isScalarTower F target e he hF hzero
  letI : Module.Finite T S :=
    homogeneousMap_moduleFinite F e he hF hzero
  let g : S →ₐ[T] Q :=
    { toRingHom := sourceMap
      commutes' := fun _ => rfl }
  let L : TensorProduct T P S →ₐ[P] Q :=
    @Algebra.TensorProduct.lift T P P S Q
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (homogeneousMap_allTarget_rees_isScalarTower F target e he hF hzero)
      (Algebra.ofId P Q) g (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hrange : Ideal.Quotient.mk I p ∈ L.range := by
      induction p using MvPolynomial.induction_on with
      | C c =>
          refine ⟨algebraMap P (TensorProduct T P S)
            (Polynomial.C c), ?_⟩
          change L (algebraMap P (TensorProduct T P S)
            (Polynomial.C c)) = _
          rw [L.commutes]
          change homogeneousMapAllTargetReesParameterRingHom F target e
            (Polynomial.C c) = _
          simp [homogeneousMapAllTargetReesParameterRingHom, I]
      | add f g hf hg =>
          rw [map_add]
          exact L.range.add_mem hf hg
      | mul_X f i hf =>
          rw [map_mul]
          apply L.range.mul_mem hf
          cases i using Fin.cases with
          | zero =>
              refine ⟨algebraMap P (TensorProduct T P S)
                Polynomial.X, ?_⟩
              change L (algebraMap P (TensorProduct T P S)
                Polynomial.X) = _
              rw [L.commutes]
              change homogeneousMapAllTargetReesParameterRingHom F target e
                Polynomial.X = _
              simp [homogeneousMapAllTargetReesParameterRingHom, I]
          | succ i =>
              refine ⟨TensorProduct.tmul T (1 : P)
                (MvPolynomial.X i), ?_⟩
              change L (TensorProduct.tmul T (1 : P)
                (MvPolynomial.X i)) = _
              simp [L, g, sourceMap, I]
              rw [MvPolynomial.rename_X]
    exact hrange
  exact Module.Finite.of_surjective L.toLinearMap hsurj
end PermanentRollout
