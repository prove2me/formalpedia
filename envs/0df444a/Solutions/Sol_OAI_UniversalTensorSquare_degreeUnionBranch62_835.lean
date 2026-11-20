-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_835
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:40:31.145015+00:00
-- url     : https://prove2.me/submissions/54f54aa0-b250-4703-b122-ca3a0460d677

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

lemma degreeUnionBranch62_835_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 44 4 degreeUnionState62_835 [4,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_835_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_835_oai
