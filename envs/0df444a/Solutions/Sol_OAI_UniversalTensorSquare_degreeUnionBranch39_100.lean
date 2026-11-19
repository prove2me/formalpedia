-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_100
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:37.703763+00:00
-- url     : https://prove2.me/submissions/b4dc1429-273c-49e9-ab9a-51cdcc565498

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

lemma degreeUnionBranch39_100_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 18 degreeUnionState39_100 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_100_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_100_oai
