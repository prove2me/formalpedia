-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_912
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:31:04.303141+00:00
-- url     : https://prove2.me/submissions/2791a042-3b3b-422c-b3ac-f6b8e55a493c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_913
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_914
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_915
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_916
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_917
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_918

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

lemma degreeUnionBranch62_912_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 8 degreeUnionState62_912 [8,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_913
  · exact degreeUnionBranch62_914
  · exact degreeUnionBranch62_915
  · exact degreeUnionBranch62_916
  · exact degreeUnionBranch62_917
  · exact degreeUnionBranch62_918

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_912_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_912_oai
