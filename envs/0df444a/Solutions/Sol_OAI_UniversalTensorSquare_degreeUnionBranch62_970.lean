-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_970
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:43:46.973344+00:00
-- url     : https://prove2.me/submissions/a11a6804-9cfc-44cc-96c3-4d38dbbd09d6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_970_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 37 4 degreeUnionState62_970 [4,10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_970_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_970_oai
