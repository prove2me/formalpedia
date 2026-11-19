-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_99
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:10:33.086545+00:00
-- url     : https://prove2.me/submissions/2a7339c7-1f19-427a-a410-49c50f1fde41

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_99_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 22 17 degreeUnionState39_99 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_99_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_99_oai
