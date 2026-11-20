-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_218
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:06:01.546972+00:00
-- url     : https://prove2.me/submissions/8616a878-7dfe-4def-95a3-a89aba963f27

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_219
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_220
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_221
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_222
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_223
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_224

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

lemma degreeUnionBranch62_218_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 9 degreeUnionState62_218 [9,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_219
  · exact degreeUnionBranch62_220
  · exact degreeUnionBranch62_221
  · exact degreeUnionBranch62_222
  · exact degreeUnionBranch62_223
  · exact degreeUnionBranch62_224

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_218_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_218_oai
