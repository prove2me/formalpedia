-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierDifferentIdeal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:53:11.798212+00:00
-- url     : https://prove2.me/submissions/4a0f6ab6-f5e1-4af2-900c-b784875169cd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreier_aeval_derivative_minpoly
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    differentIdeal P.valuationRing
        (RegularQuadraticArtinSchreierIntegralClosure P b hirr) = ⊤ := by
  let O := P.valuationRing
  let C := RegularQuadraticArtinSchreierIntegralClosure P b hirr
  let L := RegularQuadraticArtinSchreierField P b hirr
  let y : C := regularQuadraticArtinSchreierIntegralRoot P b hirr
  have hfieldAdjoin : Algebra.adjoin K
      ({algebraMap C L y} : Set L) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (regularQuadraticArtinSchreierDefiningPolynomial_monic
        P b hirr).ne_zero).adjoin_gen_eq_top
    simp only [C, L, y, coe_regularQuadraticArtinSchreierIntegralRoot,
      regularQuadraticArtinSchreierRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hmem := aeval_derivative_mem_differentIdeal O K L y hfieldAdjoin
  rw [regularQuadraticArtinSchreier_aeval_derivative_minpoly] at hmem
  exact (differentIdeal O C).eq_top_iff_one.mpr hmem
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
