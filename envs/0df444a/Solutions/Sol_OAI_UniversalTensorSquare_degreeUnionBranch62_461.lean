-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_461
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:27:32.768027+00:00
-- url     : https://prove2.me/submissions/e03ec312-ba91-4a76-9912-159a9b335668

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

lemma degreeUnionBranch62_461_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 7 degreeUnionState62_461 [7,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_461_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_461_oai
