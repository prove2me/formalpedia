-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_174
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:39:42.375222+00:00
-- url     : https://prove2.me/submissions/5149fe93-eeb3-4809-9baa-f92621e6927f

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

lemma degreeUnionBranch62_174_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 36 4 degreeUnionState62_174 [4,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_174_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_174_oai
