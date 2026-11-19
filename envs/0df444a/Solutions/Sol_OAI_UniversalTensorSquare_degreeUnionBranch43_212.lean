-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_212
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:28:45.13728+00:00
-- url     : https://prove2.me/submissions/9b57ef3b-07d7-485a-9c34-d33b3d3d7c68

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

lemma degreeUnionBranch43_212_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 27 5 degreeUnionState43_212 [5,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_212_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_212_oai
