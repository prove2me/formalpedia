-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_335
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:45:05.324576+00:00
-- url     : https://prove2.me/submissions/2586e9f2-4d58-47f1-9a26-75779217a3a0

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_335_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 27 degreeUnionState43_335 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_335_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_335_oai
