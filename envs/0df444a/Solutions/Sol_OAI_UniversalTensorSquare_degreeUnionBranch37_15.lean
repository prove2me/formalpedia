-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch37_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:14.30767+00:00
-- url     : https://prove2.me/submissions/3be46e6f-3234-4683-a3dd-4c374dd1e1cd

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

lemma degreeUnionBranch37_15_oai : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 15 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch37_15_oai := @OAI.UniversalTensorSquare.degreeUnionBranch37_15_oai
