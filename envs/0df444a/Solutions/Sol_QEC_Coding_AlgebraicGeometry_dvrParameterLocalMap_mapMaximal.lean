-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_mapMaximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:56:43.43034+00:00
-- url     : https://prove2.me/submissions/3379f612-c576-4828-a1d7-4b10b0d6df62

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterPrime_eq_spanX

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsDiscreteValuationRing V] (hπ : Irreducible π) :
    Ideal.map (dvrParameterLocalMap k V π).toRingHom
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (dvrParameterPrime k V π))) =
      IsLocalRing.maximalIdeal V := by
  let q := dvrParameterPrime k V π
  let R := Localization.AtPrime q
  let φ := dvrParameterLocalMap k V π
  have hf : φ.toRingHom.comp (algebraMap (Polynomial k) R) =
      (Polynomial.aeval π).toRingHom := by
    apply RingHom.ext
    intro r
    exact dvrParameterLocalMap_polynomial k V π r
  change Ideal.map φ.toRingHom (IsLocalRing.maximalIdeal R) = _
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := q), Ideal.map_map, hf]
  change Ideal.map (Polynomial.aeval π).toRingHom
    (dvrParameterPrime k V π) = IsLocalRing.maximalIdeal V
  rw [dvrParameterPrime_eq_spanX k V π hπ,
    Ideal.map_span, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ).symm
end QEC.Coding.AlgebraicGeometry
