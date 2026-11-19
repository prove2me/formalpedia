-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch26_90
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:31:44.096645+00:00
-- url     : https://prove2.me/submissions/3ed9f76a-1e25-45dc-a1f2-2fe8c63eaa46

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 26. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_90_oai : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 23 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch26_90_oai := @OAI.UniversalTensorSquare.degreeUnionBranch26_90_oai
