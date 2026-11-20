-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_205
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:56:35.476281+00:00
-- url     : https://prove2.me/submissions/61f7325f-ee0f-4761-9557-2ba663220482

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

lemma degreeUnionBranch62_205_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 5 degreeUnionState62_205 [5,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_205_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_205_oai
