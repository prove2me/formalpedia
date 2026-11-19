-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_601
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:25:25.676401+00:00
-- url     : https://prove2.me/submissions/8754749e-a681-4790-9adf-3d123ab5d651

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

lemma degreeUnionBranch43_601_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 10 33 degreeUnionState43_601 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_601_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_601_oai
