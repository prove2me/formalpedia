-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_311
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:09:22.806011+00:00
-- url     : https://prove2.me/submissions/074a9340-267f-4f43-a351-14b8332dce4b

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

lemma degreeUnionBranch39_311_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 14 39 38 degreeHalfRegions39 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_311_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_311_oai
