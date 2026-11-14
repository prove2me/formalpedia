-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck56_0_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:32:49.477094+00:00
-- url     : https://prove2.me/submissions/d99015b8-1c2a-4200-b312-5e610e0d119c

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

lemma degreeCheck56_0_2_oai :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck56_0_2_oai := @OAI.UniversalTensorSquare.degreeCheck56_0_2_oai
