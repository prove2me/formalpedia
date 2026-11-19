-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_721
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:40:38.908514+00:00
-- url     : https://prove2.me/submissions/d0c77ca4-9ec4-4cb9-8536-dfc008fc5498

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

lemma degreeUnionBranch43_721_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 11 32 degreeUnionState43_721 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_721_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_721_oai
