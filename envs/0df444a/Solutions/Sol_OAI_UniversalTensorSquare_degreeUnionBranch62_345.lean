-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_345
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:21:31.925706+00:00
-- url     : https://prove2.me/submissions/3c5a5121-dec6-4b64-9cee-e9b4442a4133

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_346
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_347
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_348
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_349
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_350

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

lemma degreeUnionBranch62_345_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 8 degreeUnionState62_345 [8,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_346
  · exact degreeUnionBranch62_347
  · exact degreeUnionBranch62_348
  · exact degreeUnionBranch62_349
  · exact degreeUnionBranch62_350

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_345_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_345_oai
