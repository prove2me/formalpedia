-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_393
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:57:44.093702+00:00
-- url     : https://prove2.me/submissions/bc3340af-9e0a-42f7-9cee-60b6ca20924c

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

lemma degreeUnionBranch43_393_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 28 4 degreeUnionState43_393 [4,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_393_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_393_oai
