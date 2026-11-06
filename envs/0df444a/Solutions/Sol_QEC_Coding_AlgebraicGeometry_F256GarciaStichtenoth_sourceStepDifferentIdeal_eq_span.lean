-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepDifferentIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:32.158986+00:00
-- url     : https://prove2.me/submissions/7149c94f-202e-441a-a5c0-84bad1b8ad7c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralClosure_adjoin_root_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem sourceStepReciprocalPolynomial_aeval_sourceStepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (sourceStepReciprocalRoot P x hx)
        (sourceStepReciprocalPolynomial P x hx) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of (sourceStepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (sourceStepReciprocalRoot P x hx)
      (sourceStepReciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)
private theorem sourceStep_minpoly_reciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly P.valuationRing (sourceStepReciprocalRoot P x hx) =
      sourceStepReciprocalPolynomial P x hx := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (SourceStepField P x hx)
  have hw_integral : IsIntegral P.valuationRing
      (sourceStepReciprocalRoot P x hx) := by
    have hport := (sourceStepIntegralRoot P x hx).property
    simp only [coe_sourceStepIntegralRoot] at hport ⊢
    exact hport
  have hmin_K : minpoly K (sourceStepReciprocalRoot P x hx) =
      sourceStepPolynomial P x hx := by
    simpa only [sourceStepReciprocalRoot, AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (sourceStepPolynomial_monic P x hx)
  have hmin_natDegree :
      (minpoly P.valuationRing
        (sourceStepReciprocalRoot P x hx)).natDegree = 16 := by
    calc
      (minpoly P.valuationRing
          (sourceStepReciprocalRoot P x hx)).natDegree =
          ((minpoly P.valuationRing
            (sourceStepReciprocalRoot P x hx)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hw_integral).natDegree_map _).symm
      _ = (minpoly K (sourceStepReciprocalRoot P x hx)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hw_integral]
      _ = (sourceStepPolynomial P x hx).natDegree := by rw [hmin_K]
      _ = 16 := sourceStepPolynomial_natDegree P x hx
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact sourceStepReciprocalPolynomial_monic P x hx
  · exact sourceStepReciprocalPolynomial_aeval_sourceStepReciprocalRoot P x hx
  · rw [degree_eq_natDegree
        (sourceStepReciprocalPolynomial_monic P x hx).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hw_integral),
      sourceStepReciprocalPolynomial_natDegree, hmin_natDegree]
private theorem sourceStep_minpoly_integralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly P.valuationRing (sourceStepIntegralRoot P x hx) =
      sourceStepReciprocalPolynomial P x hx := by
  calc
    minpoly P.valuationRing (sourceStepIntegralRoot P x hx) =
        minpoly P.valuationRing
          (algebraMap (SourceStepIntegralClosure P x hx)
            (SourceStepField P x hx) (sourceStepIntegralRoot P x hx)) :=
      (minpoly.algebraMap_eq
        (IsFractionRing.injective (SourceStepIntegralClosure P x hx)
          (SourceStepField P x hx))
        (sourceStepIntegralRoot P x hx)).symm
    _ = minpoly P.valuationRing (sourceStepReciprocalRoot P x hx) := by
      congr 1
    _ = sourceStepReciprocalPolynomial P x hx :=
      sourceStep_minpoly_reciprocalRoot P x hx
private theorem sourceStep_aeval_derivative_minpoly
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (sourceStepIntegralRoot P x hx)
        (derivative (minpoly P.valuationRing
          (sourceStepIntegralRoot P x hx))) =
      sourceStepIntegralUniformizer P x hx *
        sourceStepIntegralRoot P x hx ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP P.valuationRing 2 :=
    P.valuationRing.subtype.charP P.valuationRing.subtype_injective 2
  have hderivative :
      derivative (minpoly P.valuationRing (sourceStepIntegralRoot P x hx)) =
        C (sourceStepUniformizer P x hx) * X ^ 14 := by
    rw [sourceStep_minpoly_integralRoot,
      sourceStepReciprocalPolynomial]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X_pow, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  simp only [map_mul, aeval_C, aeval_X, map_pow,
    algebraMap_sourceStepUniformizer]
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
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    differentIdeal P.valuationRing (SourceStepIntegralClosure P x hx) =
      Ideal.span
        ({sourceStepIntegralUniformizer P x hx *
            sourceStepIntegralRoot P x hx ^ 14} :
          Set (SourceStepIntegralClosure P x hx)) := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let L := SourceStepField P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let hfieldAdjoin : Algebra.adjoin K
      ({algebraMap C L w} : Set L) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (sourceStepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
    simp only [C, L, w, coe_sourceStepIntegralRoot, sourceStepReciprocalRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hconductor : conductor O w = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top (by
      simpa only [O, C, w] using
        sourceStepIntegralClosure_adjoin_root_eq_top P x hx)
  have hdifferent := conductor_mul_differentIdeal O K L w hfieldAdjoin
  rw [hconductor, Ideal.top_mul,
    sourceStep_aeval_derivative_minpoly] at hdifferent
  simpa only [O, C, w] using hdifferent
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
