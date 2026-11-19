-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_670
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:30:58.06588+00:00
-- url     : https://prove2.me/submissions/0929037b-a666-4df3-a370-b5cdc6fc9ca2

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

lemma degreeUnionBranch43_670_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 14 29 degreeUnionState43_670 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_670_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_670_oai
