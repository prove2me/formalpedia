-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_145
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:35:56.641581+00:00
-- url     : https://prove2.me/submissions/4a959499-4a5f-4f70-8a1c-459a9bb214cc

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_145_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 10 25 degreeUnionState35_145 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_145_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_145_oai
