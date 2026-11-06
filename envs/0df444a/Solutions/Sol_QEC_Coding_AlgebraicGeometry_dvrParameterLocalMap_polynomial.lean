-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:31.544267+00:00
-- url     : https://prove2.me/submissions/f1aa67a9-5c73-4f03-9c77-31b2a5e26c76

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
omit [IsDomain V]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsLocalRing V] (r : Polynomial k) :
    dvrParameterLocalMap k V π
      (algebraMap (Polynomial k)
        (Localization.AtPrime (dvrParameterPrime k V π)) r) =
      Polynomial.aeval π r := by
  simp only [dvrParameterLocalMap,
    IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl
end QEC.Coding.AlgebraicGeometry
