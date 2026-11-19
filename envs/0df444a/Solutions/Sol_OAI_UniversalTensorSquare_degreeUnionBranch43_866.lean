-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_866
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:27:07.585726+00:00
-- url     : https://prove2.me/submissions/2d9f4d0e-0d49-4fc0-84d1-be7349768771

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

lemma degreeUnionBranch43_866_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 29 14 degreeUnionState43_866 [14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_866_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_866_oai
