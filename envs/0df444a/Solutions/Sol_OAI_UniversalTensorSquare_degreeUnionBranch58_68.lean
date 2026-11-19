-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:46:57.74823+00:00
-- url     : https://prove2.me/submissions/0e3b2e15-b11a-4c3e-828e-034aa1ef366a

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

lemma degreeUnionBranch58_68_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 48 10 degreeUnionState58_68 [10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_68_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_68_oai
