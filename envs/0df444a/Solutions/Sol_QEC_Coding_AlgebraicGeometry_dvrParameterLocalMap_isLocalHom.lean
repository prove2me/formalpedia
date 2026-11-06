-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:52.1481+00:00
-- url     : https://prove2.me/submissions/275526cd-cbd9-48ff-acca-544acf934f28

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_polynomial

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
omit [IsDomain V]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsLocalRing V] :
    IsLocalHom (dvrParameterLocalMap k V π).toRingHom := by
  let q := dvrParameterPrime k V π
  let R := Localization.AtPrime q
  let φ := dvrParameterLocalMap k V π
  apply IsLocalHom.mk
  intro x hx
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff R q r s).mpr
  have hs : IsUnit (φ (algebraMap (Polynomial k) R s)) :=
    (IsLocalization.map_units R s).map φ
  have he : φ (IsLocalization.mk' R r s) * φ (algebraMap (Polynomial k) R s) =
      φ (algebraMap (Polynomial k) R r) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  change IsUnit (φ (IsLocalization.mk' R r s)) at hx
  have hr := hx.mul hs
  rw [he, dvrParameterLocalMap_polynomial] at hr
  change ¬¬IsUnit (Polynomial.aeval π r)
  exact fun h => h hr
end QEC.Coding.AlgebraicGeometry
