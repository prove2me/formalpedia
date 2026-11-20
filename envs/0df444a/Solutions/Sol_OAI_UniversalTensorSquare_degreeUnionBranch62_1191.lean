-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1191
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:26:16.006247+00:00
-- url     : https://prove2.me/submissions/b5efa5c9-abb8-4af2-93b8-d762af1024a9

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

lemma degreeUnionBranch62_1191_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 7 degreeUnionState62_1191 [7,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1191_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1191_oai
