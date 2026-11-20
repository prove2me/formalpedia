-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_772
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:17:59.071918+00:00
-- url     : https://prove2.me/submissions/3fab1f16-2cdc-4ce6-b37f-accfe9e6cef9

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

lemma degreeUnionBranch62_772_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 7 degreeUnionState62_772 [7,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_772_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_772_oai
