-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_188
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:47:55.65823+00:00
-- url     : https://prove2.me/submissions/dc72e64d-483a-432a-af3b-90db83b2b29d

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_189
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_190
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_191
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_192
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_193
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_194

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

lemma degreeUnionBranch62_188_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 9 degreeUnionState62_188 [9,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_189
  · exact degreeUnionBranch62_190
  · exact degreeUnionBranch62_191
  · exact degreeUnionBranch62_192
  · exact degreeUnionBranch62_193
  · exact degreeUnionBranch62_194

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_188_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_188_oai
