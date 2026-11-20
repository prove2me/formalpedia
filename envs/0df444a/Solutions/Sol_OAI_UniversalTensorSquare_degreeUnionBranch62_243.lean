-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_243
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:18:08.555939+00:00
-- url     : https://prove2.me/submissions/ecd38de3-a0ad-4775-8145-2c102d70f61d

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_244
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_245
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_246
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_247
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_248

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

lemma degreeUnionBranch62_243_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 8 degreeUnionState62_243 [8,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_244
  · exact degreeUnionBranch62_245
  · exact degreeUnionBranch62_246
  · exact degreeUnionBranch62_247
  · exact degreeUnionBranch62_248

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_243_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_243_oai
