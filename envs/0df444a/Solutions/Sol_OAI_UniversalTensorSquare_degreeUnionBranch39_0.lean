-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:20.314058+00:00
-- url     : https://prove2.me/submissions/c1c461f0-3ce7-4e1b-903c-8e35d998773c

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

lemma degreeUnionBranch39_0_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 0 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_0_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_0_oai
