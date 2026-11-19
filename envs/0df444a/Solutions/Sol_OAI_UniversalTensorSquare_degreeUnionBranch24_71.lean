-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch24_71
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:27:08.820984+00:00
-- url     : https://prove2.me/submissions/34bc9f1f-43d8-4a79-b926-02ca3059d3ab

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 24. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_71_oai : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 10 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch24_71_oai := @OAI.UniversalTensorSquare.degreeUnionBranch24_71_oai
