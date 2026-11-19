-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_752
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:50:24.164441+00:00
-- url     : https://prove2.me/submissions/8dc7cf82-8a18-4da9-a552-faaa3d8a89b0

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

lemma degreeUnionBranch43_752_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 20 23 degreeUnionState43_752 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_752_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_752_oai
