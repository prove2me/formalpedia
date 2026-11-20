-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1140
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:03:24.259599+00:00
-- url     : https://prove2.me/submissions/9a6e2e2c-2171-41b6-abd9-2a81632956ad

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

lemma degreeUnionBranch62_1140_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 35 5 degreeUnionState62_1140 [5,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1140_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1140_oai
