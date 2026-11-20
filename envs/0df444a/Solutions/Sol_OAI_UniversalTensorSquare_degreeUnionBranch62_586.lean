-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_586
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:05:02.897551+00:00
-- url     : https://prove2.me/submissions/d8374a30-53fd-4129-be6f-656e803cd81e

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

lemma degreeUnionBranch62_586_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 18 11 degreeUnionState62_586 [11,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_586_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_586_oai
