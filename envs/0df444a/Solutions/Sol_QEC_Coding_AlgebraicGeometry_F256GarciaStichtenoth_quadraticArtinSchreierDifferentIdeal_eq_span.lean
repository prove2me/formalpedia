-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierDifferentIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:08.362671+00:00
-- url     : https://prove2.me/submissions/62ea873a-5ac2-40a4-9b4f-946846228667

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_aeval_derivative_minpoly
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    differentIdeal P.valuationRing
        (QuadraticArtinSchreierIntegralClosure P a ha) =
      Ideal.span
        ({quadraticArtinSchreierIntegralUniformizer P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let L := QuadraticArtinSchreierField P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let hfieldAdjoin : Algebra.adjoin K
      ({algebraMap C L w} : Set L) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero).adjoin_gen_eq_top
    simp only [C, L, w, coe_quadraticArtinSchreierIntegralRoot,
      quadraticArtinSchreierReciprocalRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hconductor : conductor O w = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top (by
      simpa only [O, C, w] using
        quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top P a ha)
  have hdifferent := conductor_mul_differentIdeal O K L w hfieldAdjoin
  rw [hconductor, Ideal.top_mul,
    quadraticArtinSchreier_aeval_derivative_minpoly] at hdifferent
  simpa only [O, C, w] using hdifferent
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
