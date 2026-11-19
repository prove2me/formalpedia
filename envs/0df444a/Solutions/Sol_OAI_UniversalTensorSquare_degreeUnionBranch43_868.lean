-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_868
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:31:42.854653+00:00
-- url     : https://prove2.me/submissions/4ce1ae2c-9945-4af2-9fe0-4c95897ece10

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

lemma degreeUnionBranch43_868_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 27 16 degreeUnionState43_868 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_868_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_868_oai
