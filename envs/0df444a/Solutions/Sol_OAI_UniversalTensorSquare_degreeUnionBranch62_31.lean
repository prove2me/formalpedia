-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_31
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:53:20.743115+00:00
-- url     : https://prove2.me/submissions/7a70dc5b-08db-4501-94e7-f6ca9d254d63

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

lemma degreeUnionBranch62_31_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 41 8 degreeUnionState62_31 [8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_31_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_31_oai
