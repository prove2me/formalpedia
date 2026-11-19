-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_369
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:53:22.229025+00:00
-- url     : https://prove2.me/submissions/94bac895-ec89-4ecb-8081-de1df83415d2

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

lemma degreeUnionBranch43_369_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 28 6 degreeUnionState43_369 [6,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_369_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_369_oai
