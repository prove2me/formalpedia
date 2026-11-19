-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_765
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:50:53.162688+00:00
-- url     : https://prove2.me/submissions/de2f74dd-1b29-4f0c-aef3-de0a05904bbb

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

lemma degreeUnionBranch43_765_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 7 36 degreeUnionState43_765 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_765_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_765_oai
