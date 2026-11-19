-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_119
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:23.469325+00:00
-- url     : https://prove2.me/submissions/17e3d527-f7bc-4a9e-9573-aaa614f6dfa0

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

lemma degreeUnionBranch39_119_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 2 37 degreeUnionState39_119 [37] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_119_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_119_oai
