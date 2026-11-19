-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_116
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:06.181763+00:00
-- url     : https://prove2.me/submissions/7c30a7e1-495d-458e-81c2-7a1e097107f0

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

lemma degreeUnionBranch39_116_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 5 34 degreeUnionState39_116 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_116_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_116_oai
