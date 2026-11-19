-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:37:12.440253+00:00
-- url     : https://prove2.me/submissions/767a180d-1104-4d3d-a265-2e31f54d1604

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_39_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 13 22 degreeUnionState35_39 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_39_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_39_oai
