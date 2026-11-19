-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_215
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:55:58.418937+00:00
-- url     : https://prove2.me/submissions/cc6fb8cd-ef35-450f-98e8-c1ad576ae6ae

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

lemma degreeUnionBranch39_215_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 10 29 degreeUnionState39_215 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_215_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_215_oai
