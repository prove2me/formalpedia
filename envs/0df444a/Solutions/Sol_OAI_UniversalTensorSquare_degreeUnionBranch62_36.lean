-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:27:08.296792+00:00
-- url     : https://prove2.me/submissions/8fc7efd0-8e90-4330-aefc-323289f24389

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

lemma degreeUnionBranch62_36_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 36 13 degreeUnionState62_36 [13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_36_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_36_oai
