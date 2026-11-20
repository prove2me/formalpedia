-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_309
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:53:14.407807+00:00
-- url     : https://prove2.me/submissions/2c436862-3c94-4590-9fbc-694502dcd661

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_309_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 6 degreeUnionState62_309 [6,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_309_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_309_oai
