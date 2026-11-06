-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_different_eq_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:59:53.233565+00:00
-- url     : https://prove2.me/submissions/465c40d2-f25e-4a94-b155-1c6e5ea187ff

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierDifferentIdeal_eq_span
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_map_algEquiv_eq


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (a : K) (ha : P.order a = -1)
    (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) :
    differentIdeal P.valuationRing (integralClosure P.valuationRing L) =
      Ideal.map (algebraMap P.valuationRing (integralClosure P.valuationRing L))
        (IsLocalRing.maximalIdeal P.valuationRing) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let S := QuadraticArtinSchreierField P a ha
  let B := QuadraticArtinSchreierIntegralClosure P a ha
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  let e : S ≃ₐ[K] L := quadraticSimplePoleLiteralEquiv P a ha y hy hdegree
  let σ : B ≃ₐ[O] C := AlgEquiv.mapIntegralClosure (e.restrictScalars O)
  have hmodel : differentIdeal O B =
      Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) := by
    rw [quadraticArtinSchreierDifferentIdeal_eq_span,
      map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer]
  calc
    differentIdeal O C = Ideal.map σ (differentIdeal O B) :=
      (differentIdeal_map_algEquiv_eq O B C σ).symm
    _ = Ideal.map σ (Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O)) := by
      rw [hmodel]
    _ = Ideal.map (algebraMap O C) (IsLocalRing.maximalIdeal O) := by
      change Ideal.map σ.toRingHom
        (Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O)) = _
      rw [Ideal.map_map]
      congr 1
      exact σ.toAlgHom.comp_algebraMap
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
