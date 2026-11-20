-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_351
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:26:28.357882+00:00
-- url     : https://prove2.me/submissions/815df8af-b91b-43a3-870b-0968fadcd80f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_352
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_353
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_354
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_355
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_356
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_357

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

lemma degreeUnionBranch62_351_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_351 [9,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_352
  · exact degreeUnionBranch62_353
  · exact degreeUnionBranch62_354
  · exact degreeUnionBranch62_355
  · exact degreeUnionBranch62_356
  · exact degreeUnionBranch62_357

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_351_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_351_oai
