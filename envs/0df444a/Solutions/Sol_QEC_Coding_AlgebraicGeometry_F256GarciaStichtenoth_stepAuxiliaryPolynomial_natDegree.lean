-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:54:31.321195+00:00
-- url     : https://prove2.me/submissions/533836fd-79f3-4b5c-b82a-099db050658b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (x : K) : (stepAuxiliaryPolynomial x).natDegree = 16 := by
  apply natDegree_eq_of_degree_eq_some
  rw [stepAuxiliaryPolynomial, degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := K) 16
  · calc
      ((X : K[X]) - C (x ^ 17)).degree ≤
          max (X : K[X]).degree (C (x ^ 17)).degree :=
        degree_sub_le _ _
      _ ≤ (1 : WithBot ℕ) := max_le (by simp) (degree_C_le.trans (by norm_num))
      _ < ((X : K[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
