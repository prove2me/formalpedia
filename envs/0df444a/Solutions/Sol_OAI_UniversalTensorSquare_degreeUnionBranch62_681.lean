-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_681
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:38:31.507315+00:00
-- url     : https://prove2.me/submissions/a0a1dac4-ab62-4e80-9852-b451926f9775

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

lemma degreeUnionBranch62_681_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 4 degreeUnionState62_681 [4,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_681_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_681_oai
