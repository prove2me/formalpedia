-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:30.163238+00:00
-- url     : https://prove2.me/submissions/a45a551d-24ef-43f4-940d-177732fb5a12

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

lemma degreeUnionBranch43_238_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 12 degreeUnionState43_238 [12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_238_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_238_oai
