-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_682
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:38:38.147596+00:00
-- url     : https://prove2.me/submissions/dad436e9-0fe0-4131-bf7a-1ddf8961a94e

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

lemma degreeUnionBranch62_682_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 5 degreeUnionState62_682 [5,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_682_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_682_oai
