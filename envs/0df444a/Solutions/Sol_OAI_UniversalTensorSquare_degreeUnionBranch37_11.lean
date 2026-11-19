-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch37_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:41:50.984595+00:00
-- url     : https://prove2.me/submissions/f6bdfe34-6c4a-4c08-8df4-89077a8b0a82

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 37. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch37_11_oai : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 11 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch37_11_oai := @OAI.UniversalTensorSquare.degreeUnionBranch37_11_oai
