-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:26.083189+00:00
-- url     : https://prove2.me/submissions/a7ac91f7-2bde-4858-8210-fad0a2caed6f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_1_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 1 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_1_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_1_oai
