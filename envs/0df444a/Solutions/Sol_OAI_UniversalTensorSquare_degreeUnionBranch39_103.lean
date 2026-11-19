-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_103
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:56.168202+00:00
-- url     : https://prove2.me/submissions/126702b9-49b9-4081-acb1-a23047467768

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

lemma degreeUnionBranch39_103_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 18 21 degreeUnionState39_103 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_103_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_103_oai
