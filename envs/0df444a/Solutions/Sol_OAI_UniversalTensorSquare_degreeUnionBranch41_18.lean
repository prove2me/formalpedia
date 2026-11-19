-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch41_18
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:14:03.752548+00:00
-- url     : https://prove2.me/submissions/b46a3968-0c5a-4d99-beb4-8108fc5d185f

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

lemma degreeUnionBranch41_18_oai : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 18 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch41_18_oai := @OAI.UniversalTensorSquare.degreeUnionBranch41_18_oai
