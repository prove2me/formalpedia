-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch41_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:11:07.979231+00:00
-- url     : https://prove2.me/submissions/6c0d14c4-7b73-461a-8fe8-524524ea45e2

import Mathlib
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 41. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch41_15_oai : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 15 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch41_15_oai := @OAI.UniversalTensorSquare.degreeUnionBranch41_15_oai
