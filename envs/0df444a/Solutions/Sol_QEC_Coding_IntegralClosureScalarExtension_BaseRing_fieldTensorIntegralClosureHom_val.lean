-- Prove2me | solution 1 for QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:49.021549+00:00
-- url     : https://prove2.me/submissions/2aac3b39-c0d5-4215-b33d-20652a39515e

import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
import Theorems.Thm_QEC_Coding_IntegralClosureScalarExtension_BaseRing_fieldChartTensorCancelIntegralClosure_naturality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.IntegralClosureScalarExtension
open scoped TensorProduct
noncomputable section
variable {k L B : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing B] [Algebra k B] [Algebra.IsAlgebraic k L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] QEC.Coding.IntegralClosureScalarExtension.fieldNativeBaseAlgebra
attribute [local instance] QEC.Coding.IntegralClosureScalarExtension.fieldRightBaseModule
open QEC.Coding.IntegralClosureScalarExtension.BaseRing
variable {K F B0 : Type*} [CommRing K] [CommRing F] [Algebra K F]
  [CommRing B0] [Algebra K B0]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldRightBaseModule
namespace QEC.Coding.IntegralClosureScalarExtension.BaseRing
theorem _root_.solution
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    let : Algebra (F ⊗[K] R) (F ⊗[K] B0) :=
      (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
    ∀ z : F ⊗[K] integralClosure R B0,
      (fieldTensorIntegralClosureHom (K := K) (F := F) R z).val =
        Algebra.TensorProduct.map (AlgHom.id K F)
          ((integralClosure R B0).val.restrictScalars K) z := by
  let : Algebra (F ⊗[K] R) (F ⊗[K] B0) :=
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
  dsimp only
  intro z
  change fieldChartTensorCancelEquiv (K := K) F R
    (Algebra.TensorProduct.map (AlgHom.id R (F ⊗[K] R)) (integralClosure R B0).val
      ((fieldChartTensorCancelEquiv (K := K) F R (B0 := integralClosure R B0)).symm z)) = _
  rw [fieldChartTensorCancelIntegralClosure_naturality, AlgEquiv.apply_symm_apply]
end QEC.Coding.IntegralClosureScalarExtension.BaseRing
