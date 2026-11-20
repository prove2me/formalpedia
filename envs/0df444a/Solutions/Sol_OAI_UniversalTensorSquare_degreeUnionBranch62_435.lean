-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_435
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:12.224692+00:00
-- url     : https://prove2.me/submissions/c939f9e4-bb68-4236-a88e-725312350bd6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_436
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_437
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_438
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_439
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_440
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_441

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

lemma degreeUnionBranch62_435_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 9 degreeUnionState62_435 [9,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_436
  · exact degreeUnionBranch62_437
  · exact degreeUnionBranch62_438
  · exact degreeUnionBranch62_439
  · exact degreeUnionBranch62_440
  · exact degreeUnionBranch62_441

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_435_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_435_oai
