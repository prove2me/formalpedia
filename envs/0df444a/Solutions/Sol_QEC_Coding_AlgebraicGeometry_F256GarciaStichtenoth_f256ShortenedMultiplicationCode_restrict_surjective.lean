-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_restrict_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:44.858048+00:00
-- url     : https://prove2.me/submissions/7003b2e1-cbe7-4a0a-b8a7-f0f4c12421a6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_sub_region_large
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_surjective_of_constantAlgebra_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (S : Finset (F256MultiplicationRetained i))
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    Function.Surjective (fun x : (f256ShortenedMultiplicationCode i).carrier =>
      fun j : S => x.val j.val) := by
  classical
  have honto := agEvaluation_surjective_of_constantAlgebra_eq F256
    (f256GarciaStichtenothField i)
    (π := f256GarciaStichtenothPolynomialAlgebra i)
    (ρ := f256GarciaStichtenothRatFuncAlgebra i)
    (τ := f256GarciaStichtenothPolynomialTower i)
    (φ := f256GarciaStichtenothFunctionField i)
    (s := f256GarciaStichtenothSeparable i)
    (sourceClosureDirectConstant_eq (i + 2)).symm
    (f256ShortenedMultiplicationDivisor i)
    (fun j : S => f256GarciaStichtenothSelectedRationalPlace i j.val.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp
      (Subtype.val_injective.comp Subtype.val_injective))
    (fun j => f256ShortenedMultiplicationDivisor_retained_eq_zero i j.val)
    (f256ShortenedMultiplicationDivisor_sub_region_large i S hS)
  intro values
  obtain ⟨a, ha⟩ := honto values
  refine ⟨⟨agEvaluationLinearMap (f256ShortenedMultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    (f256ShortenedMultiplicationDivisor_retained_eq_zero i) a, ⟨a, rfl⟩⟩, ?_⟩
  exact ha
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
