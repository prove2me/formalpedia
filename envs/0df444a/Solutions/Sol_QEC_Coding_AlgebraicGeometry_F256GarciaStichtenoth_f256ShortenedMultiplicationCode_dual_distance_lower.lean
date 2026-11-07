-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_dual_distance_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:39:46.027362+00:00
-- url     : https://prove2.me/submissions/3bdb8736-0217-4f77-b058-b0e8b3e5931f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_large_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_small_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothFunctionFieldGenus_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_dual_distance_numerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dual_distance_of_constantAlgebra_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (((f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256ShortenedMultiplicationCode i).dual := by
  classical
  have h := agEvaluation_dual_distance_of_constantAlgebra_eq F256 (f256GarciaStichtenothField i)
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
  rw [f256ShortenedMultiplicationDivisor_degree,
    f256GarciaStichtenothFunctionFieldGenus_eq] at h
  have hb := f256MultiplicationDivisor_dual_distance_numerator i
  have hb' : (f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i ≤
      Int.toNat (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) -
        f256MultiplicationLogicalCount i + 2 - 2 * (f256GarciaStichtenothGenus i : ℤ)) := by
    omega
  exact le_trans (WithTop.coe_le_coe.mpr hb') h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
