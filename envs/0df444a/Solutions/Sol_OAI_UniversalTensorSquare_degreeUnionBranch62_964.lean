-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_964
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:37:31.948769+00:00
-- url     : https://prove2.me/submissions/33f9a47e-b80a-4856-8cbe-2c2c67ec184e

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

lemma degreeUnionBranch62_964_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 46 5 degreeUnionState62_964 [5,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_964_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_964_oai
