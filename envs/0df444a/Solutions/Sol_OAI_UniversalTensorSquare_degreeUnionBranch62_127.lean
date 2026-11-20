-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_127
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:58:36.264757+00:00
-- url     : https://prove2.me/submissions/28a8a5ed-7e28-4ea6-bd2b-0956ebed64fb

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

lemma degreeUnionBranch62_127_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 21 8 degreeUnionState62_127 [8,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_127_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_127_oai
