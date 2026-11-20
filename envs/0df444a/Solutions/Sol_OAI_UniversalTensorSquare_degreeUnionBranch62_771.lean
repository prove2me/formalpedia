-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_771
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:12:26.00789+00:00
-- url     : https://prove2.me/submissions/b161b1e0-28b3-48c9-afd6-38ab1bc11a50

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

lemma degreeUnionBranch62_771_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 6 degreeUnionState62_771 [6,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_771_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_771_oai
