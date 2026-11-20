-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_900
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:13:27.961194+00:00
-- url     : https://prove2.me/submissions/80c8972b-1d03-472e-b7ea-e6c2a88b2190

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

lemma degreeUnionBranch62_900_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 20 9 degreeUnionState62_900 [9,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_900_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_900_oai
