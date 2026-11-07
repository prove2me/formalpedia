-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_dimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:40:31.116783+00:00
-- url     : https://prove2.me/submissions/b69af1fe-484a-4393-81ae-fe6c909f2a8f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree_lt_retained
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothFunctionFieldGenus_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_dimension_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_large_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dimension_eq_of_constantAlgebra_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    Dimension (f256PuncturedMultiplicationCode i) = Dimension (f256MultiplicationCode i) := by
  have h := agEvaluation_dimension_eq_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm (f256MultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (fun j => f256MultiplicationDivisor_selected_eq_zero i j.val)
    (f256MultiplicationDivisor_large_degree i)
    (f256MultiplicationDivisor_degree_lt_retained i)
  change (Dimension (f256PuncturedMultiplicationCode i) : ℤ) = _ at h
  rw [f256GarciaStichtenothFunctionFieldGenus_eq, ← f256MultiplicationCode_dimension_eq] at h
  exact_mod_cast h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
