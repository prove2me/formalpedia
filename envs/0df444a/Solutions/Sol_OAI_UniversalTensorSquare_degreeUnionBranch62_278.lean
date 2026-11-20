-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_278
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:35:09.773324+00:00
-- url     : https://prove2.me/submissions/a78228e4-366f-4169-b4dc-76a8341b187c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_279
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_280
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_281
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_282
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_283

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

lemma degreeUnionBranch62_278_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 8 degreeUnionState62_278 [8,8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_279
  · exact degreeUnionBranch62_280
  · exact degreeUnionBranch62_281
  · exact degreeUnionBranch62_282
  · exact degreeUnionBranch62_283

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_278_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_278_oai
