-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_227
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:59:53.615487+00:00
-- url     : https://prove2.me/submissions/caed67ae-ac23-45bb-a733-da7a8242cc98

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

lemma degreeUnionBranch39_227_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 34 5 degreeUnionState39_227 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_227_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_227_oai
