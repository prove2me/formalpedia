-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch37_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:42:08.410666+00:00
-- url     : https://prove2.me/submissions/747235bf-6dd9-45e2-98db-9e157fb405d0

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

lemma degreeUnionBranch37_14_oai : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 14 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch37_14_oai := @OAI.UniversalTensorSquare.degreeUnionBranch37_14_oai
