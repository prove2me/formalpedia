-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_454
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:16:42.052315+00:00
-- url     : https://prove2.me/submissions/82f6d4f2-63ac-429e-b1a9-02a6a8fb8d5c

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

lemma degreeUnionBranch62_454_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 6 degreeUnionState62_454 [6,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_454_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_454_oai
