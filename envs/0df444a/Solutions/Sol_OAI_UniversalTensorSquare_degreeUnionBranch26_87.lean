-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch26_87
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:31:26.39961+00:00
-- url     : https://prove2.me/submissions/9838aa91-894f-4f8c-beec-260925bdb57b

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

lemma degreeUnionBranch26_87_oai : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 20 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch26_87_oai := @OAI.UniversalTensorSquare.degreeUnionBranch26_87_oai
