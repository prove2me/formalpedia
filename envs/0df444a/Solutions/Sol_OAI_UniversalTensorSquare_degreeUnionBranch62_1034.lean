-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1034
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:05:57.422086+00:00
-- url     : https://prove2.me/submissions/3e7eec63-3657-4d48-98dc-99fd3283d2ef

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

lemma degreeUnionBranch62_1034_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 5 degreeUnionState62_1034 [5,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1034_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1034_oai
