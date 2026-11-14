-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck60_0_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:35:28.538832+00:00
-- url     : https://prove2.me/submissions/c0c09b6f-ae89-4991-bde2-026fc02020e2

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck60_0_3_oai :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck60_0_3_oai := @OAI.UniversalTensorSquare.degreeCheck60_0_3_oai
