-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_large_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:33:00.955203+00:00
-- url     : https://prove2.me/submissions/b8574961-b424-44e1-9c5f-ad439dbc95dd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_dual_distance_numerator


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) := by
  rw [f256ShortenedMultiplicationDivisor_degree]
  have h := f256MultiplicationDivisor_dual_distance_numerator i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
