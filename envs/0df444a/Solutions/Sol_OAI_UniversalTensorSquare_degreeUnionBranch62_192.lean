-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_192
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:48:08.730459+00:00
-- url     : https://prove2.me/submissions/e17a92c5-d412-450d-b845-299a657c769b

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

lemma degreeUnionBranch62_192_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 7 degreeUnionState62_192 [7,9,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_192_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_192_oai
