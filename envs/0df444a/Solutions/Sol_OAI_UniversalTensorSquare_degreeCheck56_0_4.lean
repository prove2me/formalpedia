-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck56_0_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:32:52.384114+00:00
-- url     : https://prove2.me/submissions/ec49c0ad-1e56-41ee-bac3-a2208ab354d0

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

lemma degreeCheck56_0_4_oai :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck56_0_4_oai := @OAI.UniversalTensorSquare.degreeCheck56_0_4_oai
