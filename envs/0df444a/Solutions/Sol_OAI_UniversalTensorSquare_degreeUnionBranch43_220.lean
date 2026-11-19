-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_220
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:38.553207+00:00
-- url     : https://prove2.me/submissions/d3572f9b-3762-476c-8f6c-24138fa9806f

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

lemma degreeUnionBranch43_220_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 27 4 degreeUnionState43_220 [4,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_220_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_220_oai
