-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_869
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:31:48.80396+00:00
-- url     : https://prove2.me/submissions/2cdbacd8-9d94-4f05-9bf7-598ca02335ff

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

lemma degreeUnionBranch43_869_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 26 17 degreeUnionState43_869 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_869_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_869_oai
