-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_894
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:19:25.423402+00:00
-- url     : https://prove2.me/submissions/4526e449-22c4-4e81-81ec-2d584fea5cad

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

lemma degreeUnionBranch62_894_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 3 degreeUnionState62_894 [3,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_894_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_894_oai
