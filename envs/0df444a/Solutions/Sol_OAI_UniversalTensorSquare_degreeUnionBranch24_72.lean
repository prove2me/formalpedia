-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch24_72
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:27:14.623635+00:00
-- url     : https://prove2.me/submissions/46f1aff0-cacf-4a98-97ec-53ca315d4872

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

lemma degreeUnionBranch24_72_oai : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 11 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch24_72_oai := @OAI.UniversalTensorSquare.degreeUnionBranch24_72_oai
