-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_676
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:31:33.940496+00:00
-- url     : https://prove2.me/submissions/971d91de-e700-4993-88a2-d3af942c0fdc

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

lemma degreeUnionBranch43_676_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 8 35 degreeUnionState43_676 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_676_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_676_oai
