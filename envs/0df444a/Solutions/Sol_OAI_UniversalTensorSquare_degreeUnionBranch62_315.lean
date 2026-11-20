-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_315
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:58:09.73848+00:00
-- url     : https://prove2.me/submissions/b3faaf4a-fc26-4266-a643-d1012bd00fae

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_316
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_317
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_318
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_319
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_320

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

lemma degreeUnionBranch62_315_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 8 degreeUnionState62_315 [8,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_316
  · exact degreeUnionBranch62_317
  · exact degreeUnionBranch62_318
  · exact degreeUnionBranch62_319
  · exact degreeUnionBranch62_320

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_315_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_315_oai
