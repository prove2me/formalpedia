-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_166
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:38:58.598183+00:00
-- url     : https://prove2.me/submissions/99166f29-3c29-4f62-880c-85b803cb1e04

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_167
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_168
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_169
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_170
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_171
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_172

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

lemma degreeUnionBranch62_166_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 9 degreeUnionState62_166 [9,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_167
  · exact degreeUnionBranch62_168
  · exact degreeUnionBranch62_169
  · exact degreeUnionBranch62_170
  · exact degreeUnionBranch62_171
  · exact degreeUnionBranch62_172

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_166_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_166_oai
