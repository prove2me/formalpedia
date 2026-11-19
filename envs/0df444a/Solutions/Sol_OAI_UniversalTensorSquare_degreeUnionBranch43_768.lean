-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_768
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:55:12.047174+00:00
-- url     : https://prove2.me/submissions/a61636b9-ce42-4126-bc3b-2cd3f4d9374a

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

lemma degreeUnionBranch43_768_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 4 39 degreeUnionState43_768 [39] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_768_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_768_oai
