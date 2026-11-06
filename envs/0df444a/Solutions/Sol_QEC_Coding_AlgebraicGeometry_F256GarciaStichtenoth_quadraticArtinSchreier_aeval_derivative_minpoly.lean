-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_aeval_derivative_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:50:07.034983+00:00
-- url     : https://prove2.me/submissions/c15f712d-5732-404c-ab51-d360c66a7fd9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem quadraticArtinSchreierReciprocalPolynomial_aeval_root
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Polynomial.aeval (quadraticArtinSchreierReciprocalRoot P a ha)
        (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)).comp
        (algebraMap P.valuationRing K))
      (quadraticArtinSchreierReciprocalRoot P a ha)
      (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (quadraticArtinSchreierPolynomial P a ha)
private theorem quadraticArtinSchreier_minpoly_reciprocalRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    minpoly P.valuationRing (quadraticArtinSchreierReciprocalRoot P a ha) =
      quadraticArtinSchreierReciprocalPolynomial P a ha := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierField P a ha) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (QuadraticArtinSchreierField P a ha)
  have hw_integral : IsIntegral P.valuationRing
      (quadraticArtinSchreierReciprocalRoot P a ha) := by
    have hport := (quadraticArtinSchreierIntegralRoot P a ha).property
    simp only [coe_quadraticArtinSchreierIntegralRoot] at hport ⊢
    exact hport
  have hmin_K : minpoly K (quadraticArtinSchreierReciprocalRoot P a ha) =
      quadraticArtinSchreierPolynomial P a ha := by
    simpa only [quadraticArtinSchreierReciprocalRoot,
      AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (quadraticArtinSchreierPolynomial_monic P a ha)
  have hmin_natDegree :
      (minpoly P.valuationRing
        (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree = 2 := by
    calc
      (minpoly P.valuationRing
          (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree =
          ((minpoly P.valuationRing
            (quadraticArtinSchreierReciprocalRoot P a ha)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hw_integral).natDegree_map _).symm
      _ = (minpoly K
          (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hw_integral]
      _ = (quadraticArtinSchreierPolynomial P a ha).natDegree := by
        rw [hmin_K]
      _ = 2 := quadraticArtinSchreierPolynomial_natDegree P a ha
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact quadraticArtinSchreierReciprocalPolynomial_monic P a ha
  · exact quadraticArtinSchreierReciprocalPolynomial_aeval_root P a ha
  · rw [degree_eq_natDegree
        (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hw_integral),
      quadraticArtinSchreierReciprocalPolynomial_natDegree, hmin_natDegree]
private theorem quadraticArtinSchreier_minpoly_integralRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    minpoly P.valuationRing (quadraticArtinSchreierIntegralRoot P a ha) =
      quadraticArtinSchreierReciprocalPolynomial P a ha := by
  calc
    minpoly P.valuationRing (quadraticArtinSchreierIntegralRoot P a ha) =
        minpoly P.valuationRing
          (algebraMap (QuadraticArtinSchreierIntegralClosure P a ha)
            (QuadraticArtinSchreierField P a ha)
            (quadraticArtinSchreierIntegralRoot P a ha)) :=
      (minpoly.algebraMap_eq
        (IsFractionRing.injective
          (QuadraticArtinSchreierIntegralClosure P a ha)
          (QuadraticArtinSchreierField P a ha))
        (quadraticArtinSchreierIntegralRoot P a ha)).symm
    _ = minpoly P.valuationRing
        (quadraticArtinSchreierReciprocalRoot P a ha) := by
      congr 1
    _ = quadraticArtinSchreierReciprocalPolynomial P a ha :=
      quadraticArtinSchreier_minpoly_reciprocalRoot P a ha
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
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Polynomial.aeval (quadraticArtinSchreierIntegralRoot P a ha)
        (derivative (minpoly P.valuationRing
          (quadraticArtinSchreierIntegralRoot P a ha))) =
      quadraticArtinSchreierIntegralUniformizer P a ha := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP P.valuationRing 2 :=
    P.valuationRing.subtype.charP P.valuationRing.subtype_injective 2
  have hderivative :
      derivative (minpoly P.valuationRing
        (quadraticArtinSchreierIntegralRoot P a ha)) =
      C (reciprocalUniformizer P a ha) := by
    rw [quadraticArtinSchreier_minpoly_integralRoot,
      quadraticArtinSchreierReciprocalPolynomial]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  simp only [aeval_C, algebraMap_quadraticArtinSchreierUniformizer]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
