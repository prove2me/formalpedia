-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_321
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:07:37.052152+00:00
-- url     : https://prove2.me/submissions/a21b47e5-a225-4151-9749-7309235eeea3

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_322
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_323
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_324
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_325
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_326
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_327

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

lemma degreeUnionBranch62_321_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 9 degreeUnionState62_321 [9,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_322
  · exact degreeUnionBranch62_323
  · exact degreeUnionBranch62_324
  · exact degreeUnionBranch62_325
  · exact degreeUnionBranch62_326
  · exact degreeUnionBranch62_327

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_321_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_321_oai
