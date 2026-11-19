-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_343
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:48:25.84903+00:00
-- url     : https://prove2.me/submissions/2fc483e9-239a-41f4-b0da-e3f015d5868c

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

lemma degreeUnionBranch43_343_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 8 35 degreeUnionState43_343 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_343_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_343_oai
