-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:24.330905+00:00
-- url     : https://prove2.me/submissions/ddcd8f15-8cd3-49c5-b275-87dc123ae60d

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrUniformizer_polynomialMapInjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_polynomial

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsLocalRing V] (hπ : Irreducible π) :
    Function.Injective (dvrParameterLocalMap k V π) := by
  change Function.Injective (dvrParameterLocalMap k V π).toRingHom
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (dvrParameterPrime k V π).primeCompl
    (dvrParameterLocalMap k V π).toRingHom]
  intro r s
  constructor
  · exact congrArg (dvrParameterLocalMap k V π)
  · intro h
    apply congrArg (algebraMap (Polynomial k)
      (Localization.AtPrime (dvrParameterPrime k V π)))
    apply dvrUniformizer_polynomialMapInjective k V π hπ
    change dvrParameterLocalMap k V π
      (algebraMap (Polynomial k) _ r) = dvrParameterLocalMap k V π
      (algebraMap (Polynomial k) _ s) at h
    simpa only [dvrParameterLocalMap_polynomial] using h
end QEC.Coding.AlgebraicGeometry
