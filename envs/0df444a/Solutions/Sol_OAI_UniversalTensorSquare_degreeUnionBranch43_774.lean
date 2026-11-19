-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_774
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:55:35.954163+00:00
-- url     : https://prove2.me/submissions/fad21e56-b704-4fa4-81a1-4d26b025a6f9

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

lemma degreeUnionBranch43_774_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 39 4 degreeUnionState43_774 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_774_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_774_oai
