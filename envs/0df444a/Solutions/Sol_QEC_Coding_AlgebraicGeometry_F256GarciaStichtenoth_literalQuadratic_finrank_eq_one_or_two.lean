-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.literalQuadratic_finrank_eq_one_or_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:08:56.182811+00:00
-- url     : https://prove2.me/submissions/b8d30bfa-5b16-46ee-b32f-c55da711e96b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    {K E : Type*} [_root_.Field K] [_root_.Field E] [Algebra K E]
    [FiniteDimensional K E] (a : K) (z : E)
    (hz : z ^ 2 + z = algebraMap K E a) (hgen : K⟮z⟯ = ⊤) :
    Module.finrank K E = 1 ∨ Module.finrank K E = 2 := by
  let p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X - Polynomial.C a
  have hp : p.Monic := by
    simpa only [p, sub_eq_add_neg, ← Polynomial.C_neg,
      Polynomial.C_1, one_mul] using
      (Polynomial.isMonicOfDegree_add_add_two (1 : K) (-a)).monic
  have hpdegree : p.natDegree = 2 := by
    simpa only [p, sub_eq_add_neg, ← Polynomial.C_neg,
      Polynomial.C_1, one_mul] using
      (Polynomial.isMonicOfDegree_add_add_two (1 : K) (-a)).natDegree_eq
  have hroot : Polynomial.aeval z p = 0 := by
    simpa only [p, map_sub, map_add, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, sub_eq_zero] using hz
  have hi : IsIntegral K z := ⟨p, hp, hroot⟩
  have hbound : Module.finrank K E ≤ 2 := by
    have hm := Polynomial.natDegree_le_of_dvd (minpoly.dvd K z hroot) hp.ne_zero
    rw [← IntermediateField.adjoin.finrank hi, hgen,
      IntermediateField.finrank_top', hpdegree] at hm
    exact hm
  have hpos := Module.finrank_pos (R := K) (M := E)
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
