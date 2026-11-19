-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_65
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:46:51.690032+00:00
-- url     : https://prove2.me/submissions/b84d3ca1-ee17-4b03-8f0f-56973bf7f7ee

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_65_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 51 7 degreeUnionState58_65 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_65_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_65_oai
