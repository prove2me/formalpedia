-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_578
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:54:34.510398+00:00
-- url     : https://prove2.me/submissions/66fd3e41-ef66-42ca-92d1-949acf8e741f

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

lemma degreeUnionBranch62_578_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 3 degreeUnionState62_578 [3,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_578_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_578_oai
