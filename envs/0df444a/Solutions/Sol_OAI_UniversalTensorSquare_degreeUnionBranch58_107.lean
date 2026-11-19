-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_107
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:36:59.586472+00:00
-- url     : https://prove2.me/submissions/96a1d4ff-6514-4830-ab3d-f7b1ac632b0a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_107_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 36 10 degreeUnionState58_107 [10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_107_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_107_oai
