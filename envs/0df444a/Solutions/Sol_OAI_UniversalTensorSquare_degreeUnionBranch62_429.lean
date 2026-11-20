-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_429
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:05:07.692197+00:00
-- url     : https://prove2.me/submissions/82802779-b1bc-463d-ad3d-b00a2c3c6a37

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_430
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_431
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_432
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_433
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_434

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

lemma degreeUnionBranch62_429_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 8 degreeUnionState62_429 [8,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_430
  · exact degreeUnionBranch62_431
  · exact degreeUnionBranch62_432
  · exact degreeUnionBranch62_433
  · exact degreeUnionBranch62_434

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_429_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_429_oai
