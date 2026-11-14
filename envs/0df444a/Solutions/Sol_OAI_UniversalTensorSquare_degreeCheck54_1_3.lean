-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck54_1_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:31:40.667595+00:00
-- url     : https://prove2.me/submissions/0b39b624-22c1-44dd-b6ec-470b1c6cfa76

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck54_1_3_oai :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 2 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck54_1_3_oai := @OAI.UniversalTensorSquare.degreeCheck54_1_3_oai
