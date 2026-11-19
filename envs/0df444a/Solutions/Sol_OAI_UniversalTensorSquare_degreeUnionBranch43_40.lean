-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_40
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:31.893136+00:00
-- url     : https://prove2.me/submissions/0de25a21-b898-4238-9dd3-32826c53e837

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

lemma degreeUnionBranch43_40_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 24 7 degreeUnionState43_40 [7,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_40_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_40_oai
