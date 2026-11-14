-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck60_3_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:36:48.743205+00:00
-- url     : https://prove2.me/submissions/ed621f4f-d208-4070-8f56-31ee7526c488

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

lemma degreeCheck60_3_0_oai :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 4 1 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck60_3_0_oai := @OAI.UniversalTensorSquare.degreeCheck60_3_0_oai
