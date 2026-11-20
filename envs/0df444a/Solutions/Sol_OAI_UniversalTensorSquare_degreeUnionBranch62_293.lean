-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_293
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:43:52.905201+00:00
-- url     : https://prove2.me/submissions/24218e66-b29d-4a49-a39d-8d2101656b25

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_294
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_295
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_296
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_297
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_298

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

lemma degreeUnionBranch62_293_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 8 degreeUnionState62_293 [8,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_294
  · exact degreeUnionBranch62_295
  · exact degreeUnionBranch62_296
  · exact degreeUnionBranch62_297
  · exact degreeUnionBranch62_298

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_293_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_293_oai
