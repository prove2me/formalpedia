-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_117
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:12.012732+00:00
-- url     : https://prove2.me/submissions/7d3eac19-d80b-4f53-900e-3a397b35cb07

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

lemma degreeUnionBranch39_117_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 4 35 degreeUnionState39_117 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_117_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_117_oai
