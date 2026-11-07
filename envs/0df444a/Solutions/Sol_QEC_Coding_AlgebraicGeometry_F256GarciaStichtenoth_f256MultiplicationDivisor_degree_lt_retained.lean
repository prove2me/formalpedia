-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree_lt_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:53.898196+00:00
-- url     : https://prove2.me/submissions/c443ea33-64a9-4833-b001-1dc7aff93845

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree_upper


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) <
      Fintype.card (F256MultiplicationRetained i) := by
  rw [f256MultiplicationRetained_card]
  have h := f256MultiplicationDivisor_degree_upper i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
