-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:50.061417+00:00
-- url     : https://prove2.me/submissions/3b50e0ec-ca26-4449-ac17-2d909a4c7321

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_degree_eq_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) =
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) -
        f256MultiplicationLogicalCount i := by
  rw [f256ShortenedMultiplicationDivisor, Divisor.degree_sub,
    evaluationDivisor_degree_eq_card, Fintype.card_fin]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
