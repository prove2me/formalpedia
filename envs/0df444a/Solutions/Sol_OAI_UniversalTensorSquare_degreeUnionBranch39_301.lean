-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_301
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:05:17.382777+00:00
-- url     : https://prove2.me/submissions/cd41affb-afd3-4aba-bfb1-b0f03442d4bd

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

lemma degreeUnionBranch39_301_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 7 32 degreeUnionState39_301 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_301_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_301_oai
