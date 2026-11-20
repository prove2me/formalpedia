-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_848
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:55:56.352799+00:00
-- url     : https://prove2.me/submissions/47f561ff-4299-4571-a9e1-f1c7fcfecd37

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_849
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_850
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_851
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_852
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_853

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

lemma degreeUnionBranch62_848_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 8 degreeUnionState62_848 [8,8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_849
  · exact degreeUnionBranch62_850
  · exact degreeUnionBranch62_851
  · exact degreeUnionBranch62_852
  · exact degreeUnionBranch62_853

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_848_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_848_oai
