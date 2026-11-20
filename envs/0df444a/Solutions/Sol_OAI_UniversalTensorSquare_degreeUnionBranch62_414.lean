-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_414
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:56:45.878998+00:00
-- url     : https://prove2.me/submissions/81a1036a-7c6e-4137-bbf2-2dc19643805e

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_415
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_416
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_417
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_418
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_419

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

lemma degreeUnionBranch62_414_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 8 degreeUnionState62_414 [8,8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_415
  · exact degreeUnionBranch62_416
  · exact degreeUnionBranch62_417
  · exact degreeUnionBranch62_418
  · exact degreeUnionBranch62_419

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_414_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_414_oai
