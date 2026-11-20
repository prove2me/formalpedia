-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_299
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:48:39.277867+00:00
-- url     : https://prove2.me/submissions/ffb135d3-d642-4a2f-a7c2-ea0f099c1efd

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_300
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_301
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_302
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_303
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_304
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_305

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

lemma degreeUnionBranch62_299_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 9 degreeUnionState62_299 [9,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_300
  · exact degreeUnionBranch62_301
  · exact degreeUnionBranch62_302
  · exact degreeUnionBranch62_303
  · exact degreeUnionBranch62_304
  · exact degreeUnionBranch62_305

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_299_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_299_oai
