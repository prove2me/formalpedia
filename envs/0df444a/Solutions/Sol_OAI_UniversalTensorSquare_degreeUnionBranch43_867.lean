-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_867
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:27:13.806384+00:00
-- url     : https://prove2.me/submissions/08eb15ed-4d6c-4f20-94db-c9ca617cd76f

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

lemma degreeUnionBranch43_867_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 28 15 degreeUnionState43_867 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_867_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_867_oai
