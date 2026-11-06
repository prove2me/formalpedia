-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:26.647833+00:00
-- url     : https://prove2.me/submissions/62bdd08a-044c-4b5d-af2e-550ed84f7f68

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
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



set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Module.finrank K (RegularQuadraticArtinSchreierField P b hirr) = 2 := by
  calc
    Module.finrank K (RegularQuadraticArtinSchreierField P b hirr) =
        (AdjoinRoot.powerBasis
          (regularQuadraticArtinSchreierDefiningPolynomial_monic
            P b hirr).ne_zero).dim :=
      PowerBasis.finrank _
    _ = (regularQuadraticArtinSchreierDefiningPolynomial P b hirr).natDegree := rfl
    _ = 2 := by
      simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using
        regularQuadraticArtinSchreierPolynomial_natDegree P b
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
