-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_744
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:45:33.688646+00:00
-- url     : https://prove2.me/submissions/29d80f16-1061-4a84-bb33-8869ad467315

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

lemma degreeUnionBranch43_744_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 28 15 degreeUnionState43_744 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_744_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_744_oai
