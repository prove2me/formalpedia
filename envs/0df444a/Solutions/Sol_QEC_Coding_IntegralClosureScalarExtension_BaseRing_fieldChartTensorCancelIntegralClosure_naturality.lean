-- Prove2me | solution 1 for QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldChartTensorCancelIntegralClosure_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:28:13.735234+00:00
-- url     : https://prove2.me/submissions/906f670e-e487-4723-a999-bd09de8c4c4c

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
theorem _root_.solution (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0]
    (z : (E ⊗[K] R) ⊗[R] integralClosure R B0) :
    fieldChartTensorCancelEquiv (K := K) E R
      (Algebra.TensorProduct.map (AlgHom.id R (E ⊗[K] R)) (integralClosure R B0).val z) =
    Algebra.TensorProduct.map (AlgHom.id K E)
      ((integralClosure R B0).val.restrictScalars K)
      (fieldChartTensorCancelEquiv (K := K) E R z) := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s c =>
    induction s with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul a r =>
      simp [fieldChartTensorCancelEquiv_tmul]
end QEC.Coding.IntegralClosureScalarExtension.BaseRing
