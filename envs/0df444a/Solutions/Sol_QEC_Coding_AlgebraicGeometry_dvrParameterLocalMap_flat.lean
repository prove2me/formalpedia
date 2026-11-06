-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_flat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:36.166237+00:00
-- url     : https://prove2.me/submissions/ffc5ac87-34f8-423d-9b25-2e6d4b59b32f

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_injective

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsLocalRing V] (hπ : Irreducible π) :
    (dvrParameterLocalMap k V π).toRingHom.Flat := by
  let R := Localization.AtPrime (dvrParameterPrime k V π)
  let : Algebra R V := (dvrParameterLocalMap k V π).toRingHom.toAlgebra
  change (algebraMap R V).Flat
  rw [RingHom.flat_algebraMap_iff]
  let : FaithfulSMul R V := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (dvrParameterLocalMap_injective k V π hπ)
  infer_instance
end QEC.Coding.AlgebraicGeometry
