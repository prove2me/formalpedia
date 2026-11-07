-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_dimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:39:45.277696+00:00
-- url     : https://prove2.me/submissions/751994dc-c0bc-4823-a462-b608bc7011e9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_large_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_small_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothFunctionFieldGenus_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_dimension_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dimension_eq_of_constantAlgebra_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    Dimension (f256ShortenedMultiplicationCode i) + f256MultiplicationLogicalCount i =
      Dimension (f256MultiplicationCode i) := by
  have h := agEvaluation_dimension_eq_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm (f256ShortenedMultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (f256ShortenedMultiplicationDivisor_retained_eq_zero i)
    (f256ShortenedMultiplicationDivisor_large_degree i)
    (f256ShortenedMultiplicationDivisor_small_degree i)
  change (Dimension (f256ShortenedMultiplicationCode i) : ℤ) = _ at h
  rw [f256ShortenedMultiplicationDivisor_degree,
    f256GarciaStichtenothFunctionFieldGenus_eq] at h
  have hfull := f256MultiplicationCode_dimension_eq i
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
