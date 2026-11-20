-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_886
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:18:58.803746+00:00
-- url     : https://prove2.me/submissions/ca5a42f9-a5c8-4837-a389-5d723361ff8f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_887
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_888
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_889
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_890
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_891
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_892

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

lemma degreeUnionBranch62_886_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 8 degreeUnionState62_886 [8,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_887
  · exact degreeUnionBranch62_888
  · exact degreeUnionBranch62_889
  · exact degreeUnionBranch62_890
  · exact degreeUnionBranch62_891
  · exact degreeUnionBranch62_892

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_886_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_886_oai
