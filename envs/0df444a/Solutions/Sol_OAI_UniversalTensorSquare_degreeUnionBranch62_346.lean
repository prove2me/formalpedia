-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_346
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:12:39.408868+00:00
-- url     : https://prove2.me/submissions/bd1e7bf5-94db-44ef-9094-93d8d8fef85c

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

lemma degreeUnionBranch62_346_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 4 degreeUnionState62_346 [4,8,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_346_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_346_oai
