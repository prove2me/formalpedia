-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_646
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:27:23.482175+00:00
-- url     : https://prove2.me/submissions/5130e9eb-9382-406a-81ef-77910c798c8c

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

lemma degreeUnionBranch62_646_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 20 10 degreeUnionState62_646 [10,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_646_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_646_oai
