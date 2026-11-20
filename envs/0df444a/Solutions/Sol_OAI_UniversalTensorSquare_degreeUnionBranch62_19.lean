-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:45:18.543152+00:00
-- url     : https://prove2.me/submissions/cf3c1b53-f64f-4dd3-a41e-88287dce23bd

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

lemma degreeUnionBranch62_19_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 45 5 degreeUnionState62_19 [5,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_19_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_19_oai
