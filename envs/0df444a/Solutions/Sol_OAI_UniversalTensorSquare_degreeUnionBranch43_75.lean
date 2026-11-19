-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_75
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:45:58.284884+00:00
-- url     : https://prove2.me/submissions/3a91b48b-ad2b-465a-b43c-986741709b29

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_75_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 11 degreeUnionState43_75 [11,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_75_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_75_oai
