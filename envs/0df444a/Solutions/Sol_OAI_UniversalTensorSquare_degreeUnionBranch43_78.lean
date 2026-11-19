-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_78
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:00:25.697765+00:00
-- url     : https://prove2.me/submissions/187ece03-2443-4500-b68d-751252a4b8b9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_78_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 14 14 degreeUnionState43_78 [14,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_78_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_78_oai
