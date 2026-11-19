-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_218
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:56:15.876964+00:00
-- url     : https://prove2.me/submissions/10bbbe14-c6ae-4891-9265-2a0821ea6733

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_218_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 7 32 degreeUnionState39_218 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_218_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_218_oai
