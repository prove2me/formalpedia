-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationCode_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:39:37.651916+00:00
-- url     : https://prove2.me/submissions/fbe82ac0-d93c-428f-aaae-86b4d4ef6ad4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_mem_agEvaluation_sub_divisor_iff_shortened


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (w : Word F256 (F256MultiplicationRetained i)) :
    w ∈ (f256ShortenedMultiplicationCode i).carrier ↔
      ∃ x ∈ (f256MultiplicationCode i).carrier,
        (∀ a, x (f256MultiplicationPivot i a) = 0) ∧
        (fun j : F256MultiplicationRetained i => x j.val) = w :=
  mem_agEvaluation_sub_divisor_iff_shortened (f256MultiplicationDivisor i)
    (f256GarciaStichtenothSelectedRationalPlace i)
    (f256GarciaStichtenothSelectedPlace_injective i)
    (f256MultiplicationDivisor_selected_eq_zero i) (f256MultiplicationPivot i) w
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
