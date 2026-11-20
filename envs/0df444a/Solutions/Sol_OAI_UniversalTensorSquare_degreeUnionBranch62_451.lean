-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_451
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:22.567663+00:00
-- url     : https://prove2.me/submissions/27f8afe0-fa52-4054-b10c-ff107859749c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_452
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_453
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_454
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_455
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_456

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_451_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 8 degreeUnionState62_451 [8,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_452
  · exact degreeUnionBranch62_453
  · exact degreeUnionBranch62_454
  · exact degreeUnionBranch62_455
  · exact degreeUnionBranch62_456

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_451_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_451_oai
