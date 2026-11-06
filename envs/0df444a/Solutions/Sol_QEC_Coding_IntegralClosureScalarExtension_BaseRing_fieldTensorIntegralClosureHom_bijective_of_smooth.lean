-- Prove2me | solution 1 for QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_bijective_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:53.241862+00:00
-- url     : https://prove2.me/submissions/7d22328d-c3fa-4ce9-85e5-ef0ed9ce9351

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
theorem _root_.solution [Algebra.Smooth K F]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    Function.Bijective (fieldTensorIntegralClosureHom (K := K) (F := F) (B0 := B0) R) := by
  let S := F ⊗[K] R
  let : Algebra S (F ⊗[K] B0) :=
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
  let : Algebra.Smooth R (R ⊗[K] F) := inferInstance
  let : Algebra.Smooth R S := Algebra.Smooth.of_equiv (R := R)
    (A := R ⊗[K] F) (B := S) (fieldBaseChangeRightAlgEquiv (K := K) F R)
  let e := fieldChartTensorCancelBaseAlgEquiv (K := K) F R (B0 := B0)
  exact e.mapIntegralClosure.bijective.comp
    ((TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := B0)).comp
      (fieldChartTensorCancelEquiv (K := K) F R (B0 := integralClosure R B0)).symm.bijective)
end QEC.Coding.IntegralClosureScalarExtension.BaseRing
