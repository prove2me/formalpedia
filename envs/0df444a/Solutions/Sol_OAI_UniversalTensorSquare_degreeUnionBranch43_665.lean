-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_665
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:30:27.157288+00:00
-- url     : https://prove2.me/submissions/9b995822-982a-4226-8af2-2882fadf3818

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

lemma degreeUnionBranch43_665_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 19 24 degreeUnionState43_665 [24] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_665_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_665_oai
