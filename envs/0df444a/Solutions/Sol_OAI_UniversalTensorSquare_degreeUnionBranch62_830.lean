-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_830
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:40:10.665298+00:00
-- url     : https://prove2.me/submissions/b9582f4d-9185-44c4-a267-cf851fb4b08f

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

lemma degreeUnionBranch62_830_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 10 degreeUnionState62_830 [10,13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_830_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_830_oai
