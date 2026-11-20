-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_916
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:25:14.08207+00:00
-- url     : https://prove2.me/submissions/4befdd50-843a-42e0-b17a-5c3ecac1a235

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

lemma degreeUnionBranch62_916_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 6 degreeUnionState62_916 [6,8,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_916_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_916_oai
