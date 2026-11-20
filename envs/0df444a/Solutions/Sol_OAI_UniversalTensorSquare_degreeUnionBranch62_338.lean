-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_338
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:12:32.935364+00:00
-- url     : https://prove2.me/submissions/b2e58855-2e20-41bb-89ca-d0bada8f29c3

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_338_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 5 degreeUnionState62_338 [5,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_338_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_338_oai
