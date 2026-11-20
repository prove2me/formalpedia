-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1315
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:21:02.153662+00:00
-- url     : https://prove2.me/submissions/26c3e869-9297-4cc1-84f0-2a077b846d1e

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

lemma degreeUnionBranch62_1315_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 7 degreeUnionState62_1315 [7,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1315_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1315_oai
