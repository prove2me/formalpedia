-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_207
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:25:13.548473+00:00
-- url     : https://prove2.me/submissions/3cfe51da-1246-4ae1-a859-c6671db48832

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

lemma degreeUnionBranch43_207_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 8 degreeUnionState43_207 [8,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_207_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_207_oai
