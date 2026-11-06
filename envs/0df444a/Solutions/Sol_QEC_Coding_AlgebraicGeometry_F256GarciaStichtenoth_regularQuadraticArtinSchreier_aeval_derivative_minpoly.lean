-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_aeval_derivative_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:27.486822+00:00
-- url     : https://prove2.me/submissions/33809e18-eae4-4db9-b1c1-2db9e8c3506b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem regularQuadraticArtinSchreierIntegralPolynomial_aeval_root
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Polynomial.aeval (regularQuadraticArtinSchreierRoot P b hirr)
        (regularQuadraticArtinSchreierIntegralPolynomial P b) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)).comp
        (algebraMap P.valuationRing K))
      (regularQuadraticArtinSchreierRoot P b hirr)
      (regularQuadraticArtinSchreierIntegralPolynomial P b) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)
private theorem regularQuadraticArtinSchreier_minpoly_root
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    minpoly P.valuationRing (regularQuadraticArtinSchreierRoot P b hirr) =
      regularQuadraticArtinSchreierIntegralPolynomial P b := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing
      (RegularQuadraticArtinSchreierField P b hirr) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (RegularQuadraticArtinSchreierField P b hirr)
  have hy_integral : IsIntegral P.valuationRing
      (regularQuadraticArtinSchreierRoot P b hirr) := by
    exact (regularQuadraticArtinSchreierIntegralRoot P b hirr).property
  have hmin_K : minpoly K (regularQuadraticArtinSchreierRoot P b hirr) =
      regularQuadraticArtinSchreierPolynomial P b := by
    have hport := AdjoinRoot.minpoly_powerBasis_gen_of_monic
      (regularQuadraticArtinSchreierDefiningPolynomial_monic P b hirr)
    simp only [regularQuadraticArtinSchreierRoot,
      regularQuadraticArtinSchreierDefiningPolynomial,
      AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hmin_natDegree :
      (minpoly P.valuationRing
        (regularQuadraticArtinSchreierRoot P b hirr)).natDegree = 2 := by
    calc
      (minpoly P.valuationRing
          (regularQuadraticArtinSchreierRoot P b hirr)).natDegree =
          ((minpoly P.valuationRing
            (regularQuadraticArtinSchreierRoot P b hirr)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hy_integral).natDegree_map _).symm
      _ = (minpoly K
          (regularQuadraticArtinSchreierRoot P b hirr)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hy_integral]
      _ = (regularQuadraticArtinSchreierPolynomial P b).natDegree := by
        rw [hmin_K]
      _ = 2 := regularQuadraticArtinSchreierPolynomial_natDegree P b
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact regularQuadraticArtinSchreierIntegralPolynomial_monic P b
  · exact regularQuadraticArtinSchreierIntegralPolynomial_aeval_root
      P b hirr
  · rw [degree_eq_natDegree
        (regularQuadraticArtinSchreierIntegralPolynomial_monic P b).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hy_integral),
      regularQuadraticArtinSchreierIntegralPolynomial_natDegree,
      hmin_natDegree]
private theorem regularQuadraticArtinSchreier_minpoly_integralRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    minpoly P.valuationRing
        (regularQuadraticArtinSchreierIntegralRoot P b hirr) =
      regularQuadraticArtinSchreierIntegralPolynomial P b := by
  calc
    minpoly P.valuationRing
        (regularQuadraticArtinSchreierIntegralRoot P b hirr) =
        minpoly P.valuationRing
          (algebraMap
            (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
            (RegularQuadraticArtinSchreierField P b hirr)
            (regularQuadraticArtinSchreierIntegralRoot P b hirr)) :=
      (minpoly.algebraMap_eq
        (IsFractionRing.injective
          (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
          (RegularQuadraticArtinSchreierField P b hirr))
        (regularQuadraticArtinSchreierIntegralRoot P b hirr)).symm
    _ = minpoly P.valuationRing
        (regularQuadraticArtinSchreierRoot P b hirr) := by
      congr 1
    _ = regularQuadraticArtinSchreierIntegralPolynomial P b :=
      regularQuadraticArtinSchreier_minpoly_root P b hirr
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Polynomial.aeval (regularQuadraticArtinSchreierIntegralRoot P b hirr)
        (derivative (minpoly P.valuationRing
          (regularQuadraticArtinSchreierIntegralRoot P b hirr))) = 1 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP P.valuationRing 2 :=
    P.valuationRing.subtype.charP P.valuationRing.subtype_injective 2
  have hderivative :
      derivative (minpoly P.valuationRing
        (regularQuadraticArtinSchreierIntegralRoot P b hirr)) = 1 := by
    rw [regularQuadraticArtinSchreier_minpoly_integralRoot,
      regularQuadraticArtinSchreierIntegralPolynomial]
    simp only [derivative_add, derivative_X_pow, derivative_X, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  simp
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
