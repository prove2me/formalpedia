-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_799
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:24:10.42465+00:00
-- url     : https://prove2.me/submissions/9ec69e92-d77e-4afd-930e-708c4b35413a

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

lemma degreeUnionBranch62_799_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 20 9 degreeUnionState62_799 [9,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_799_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_799_oai
