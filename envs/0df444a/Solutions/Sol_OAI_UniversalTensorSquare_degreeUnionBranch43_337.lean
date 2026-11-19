-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_337
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:45:17.319521+00:00
-- url     : https://prove2.me/submissions/e00e042f-f02d-4824-86d6-c58963003098

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

lemma degreeUnionBranch43_337_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 14 29 degreeUnionState43_337 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_337_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_337_oai
