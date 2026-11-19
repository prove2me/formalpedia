-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_167
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:19:08.224027+00:00
-- url     : https://prove2.me/submissions/08b6c8ca-05ff-4d0f-9bb8-57ecc5625a27

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

lemma degreeUnionBranch43_167_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 15 28 degreeUnionState43_167 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_167_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_167_oai
