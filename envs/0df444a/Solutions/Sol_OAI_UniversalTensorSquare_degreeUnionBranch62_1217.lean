-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1217
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:39:08.346679+00:00
-- url     : https://prove2.me/submissions/8e5567ff-8a1b-4ed3-a994-24c8d40104b3

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

lemma degreeUnionBranch62_1217_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 5 degreeUnionState62_1217 [5,8,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1217_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1217_oai
