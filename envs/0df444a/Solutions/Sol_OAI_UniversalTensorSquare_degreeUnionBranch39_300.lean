-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_300
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:05:11.547808+00:00
-- url     : https://prove2.me/submissions/9f48e4bd-1f80-4237-b2d4-c0e25266c089

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

lemma degreeUnionBranch39_300_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 8 31 degreeUnionState39_300 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_300_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_300_oai
