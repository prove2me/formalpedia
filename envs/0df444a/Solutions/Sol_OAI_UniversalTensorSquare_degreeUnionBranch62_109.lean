-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_109
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:32:44.990922+00:00
-- url     : https://prove2.me/submissions/b92ad85d-1856-493a-994f-ce3177965386

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

lemma degreeUnionBranch62_109_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 5 degreeUnionState62_109 [5,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_109_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_109_oai
