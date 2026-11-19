-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_228
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:30:27.007074+00:00
-- url     : https://prove2.me/submissions/5fb1c898-747d-44e5-939c-1934ff51b6ca

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

lemma degreeUnionBranch43_228_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 12 degreeUnionState43_228 [12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_228_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_228_oai
