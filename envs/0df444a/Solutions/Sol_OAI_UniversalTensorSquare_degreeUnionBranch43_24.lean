-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:42.805895+00:00
-- url     : https://prove2.me/submissions/1c4a2247-95ce-4010-ba77-6fa4c1a7120c

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

lemma degreeUnionBranch43_24_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 27 6 degreeUnionState43_24 [6,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_24_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_24_oai
