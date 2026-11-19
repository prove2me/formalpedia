-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_306
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:05:46.622988+00:00
-- url     : https://prove2.me/submissions/401467e0-a635-476b-8251-e9ab6446ef36

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

lemma degreeUnionBranch39_306_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 2 37 degreeUnionState39_306 [37] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_306_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_306_oai
