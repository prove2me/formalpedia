-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck56_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:34:28.135531+00:00
-- url     : https://prove2.me/submissions/094e0a59-5e61-45d6-9417-e3be28518f99

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck56_3_2_oai :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck56_3_2_oai := @OAI.UniversalTensorSquare.degreeCheck56_3_2_oai
