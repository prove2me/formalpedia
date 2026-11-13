-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck151_2_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:27.748516+00:00
-- url     : https://prove2.me/submissions/cc5ac214-1f5e-4641-92e3-0b6581e95fc1

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck151_2_0_oai :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck151_2_0_oai := @OAI.UniversalTensorSquare.degreeCheck151_2_0_oai
