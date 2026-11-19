-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch37_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:41:45.012999+00:00
-- url     : https://prove2.me/submissions/e25869a2-35c4-426f-abf5-d196644acbd5

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 37. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch37_10_oai : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 10 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch37_10_oai := @OAI.UniversalTensorSquare.degreeUnionBranch37_10_oai
