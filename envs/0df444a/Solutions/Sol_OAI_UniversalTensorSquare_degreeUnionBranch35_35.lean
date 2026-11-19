-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:36:49.221574+00:00
-- url     : https://prove2.me/submissions/1d9001e3-9e8b-473c-81b5-3705103b2188

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_35_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 17 18 degreeUnionState35_35 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_35_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_35_oai
