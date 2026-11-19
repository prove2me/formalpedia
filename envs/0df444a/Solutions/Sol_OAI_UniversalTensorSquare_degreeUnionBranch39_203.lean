-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_203
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:52:03.059438+00:00
-- url     : https://prove2.me/submissions/4772b69b-1d78-415e-8b67-583bf785f2e1

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

lemma degreeUnionBranch39_203_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 22 17 degreeUnionState39_203 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_203_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_203_oai
