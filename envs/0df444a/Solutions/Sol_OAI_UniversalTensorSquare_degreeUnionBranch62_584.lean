-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_584
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:00:02.87669+00:00
-- url     : https://prove2.me/submissions/c583496f-00ad-4e61-b146-1c92aefe91e1

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

lemma degreeUnionBranch62_584_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 20 9 degreeUnionState62_584 [9,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_584_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_584_oai
