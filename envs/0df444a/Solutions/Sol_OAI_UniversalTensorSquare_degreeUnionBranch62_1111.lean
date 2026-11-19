-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1111
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:48:48.102413+00:00
-- url     : https://prove2.me/submissions/50105941-a992-4c81-a70a-29ece1730faf

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

lemma degreeUnionBranch62_1111_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 3 degreeUnionState62_1111 [3,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1111_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1111_oai
