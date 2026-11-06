-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.rational_differentialGenerator_order_of_order_X_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:02:24.653081+00:00
-- url     : https://prove2.me/submissions/15b4157b-021c-4990-94f3-4b4b677407ed

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_generator_rationalAdic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
variable [Finite k]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (R : GlobalPlace k (RatFunc k)) (hX : R.order RatFunc.X = 0) :
    differentialOrder R (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  obtain ⟨p, rfl⟩ := (GlobalPlace.rationalPlaceEquiv (k := k)).surjective R
  cases p with
  | none =>
    change (GlobalPlace.rationalInfinity k).order RatFunc.X = 0 at hX
    rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      k RatFunc.X RatFunc.X_ne_zero, RatFunc.intDegree_X] at hX
    norm_num at hX
  | some p => exact Differential.differentialOrder_generator_rationalAdic p
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
