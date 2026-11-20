-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:40:02.380537+00:00
-- url     : https://prove2.me/submissions/d4a147d3-523f-4c66-8162-1c806a312d33

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

lemma degreeUnionBranch62_29_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 43 6 degreeUnionState62_29 [6,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_29_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_29_oai
