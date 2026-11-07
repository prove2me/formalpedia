-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:40:27.106195+00:00
-- url     : https://prove2.me/submissions/2a2528ca-8b4b-4575-acd7-28f5112c0cb5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (w : Word F256 (F256MultiplicationRetained i)) :
    w ∈ (f256PuncturedMultiplicationCode i).carrier ↔
      ∃ x ∈ (f256MultiplicationCode i).carrier,
        (fun j : F256MultiplicationRetained i => x j.val) = w := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨agEvaluationLinearMap (f256MultiplicationDivisor i)
      (f256GarciaStichtenothSelectedRationalPlace i)
      (f256MultiplicationDivisor_selected_eq_zero i) f, ⟨f, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨f, rfl⟩, h⟩
    exact ⟨f, h⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
