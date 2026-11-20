-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:27:19.569178+00:00
-- url     : https://prove2.me/submissions/d85745f9-b351-4f37-bc2b-d2d108b5fd62

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

lemma degreeUnionBranch62_46_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 13 degreeUnionState62_46 [13,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_46_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_46_oai
