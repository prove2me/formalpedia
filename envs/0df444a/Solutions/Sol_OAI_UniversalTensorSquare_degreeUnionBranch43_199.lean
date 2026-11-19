-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_199
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:31.763899+00:00
-- url     : https://prove2.me/submissions/32509a87-52dc-4f77-b63c-e968c608c65e

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

lemma degreeUnionBranch43_199_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 19 6 degreeUnionState43_199 [6,9,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_199_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_199_oai
