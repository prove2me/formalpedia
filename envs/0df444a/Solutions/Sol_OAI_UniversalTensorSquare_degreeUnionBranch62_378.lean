-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_378
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:38:27.21588+00:00
-- url     : https://prove2.me/submissions/646a3625-635b-43c8-96a0-e92afeb1316c

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

lemma degreeUnionBranch62_378_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 12 degreeUnionState62_378 [12,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_378_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_378_oai
