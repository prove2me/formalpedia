-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_457
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:26:58.905531+00:00
-- url     : https://prove2.me/submissions/cec7807b-131d-483c-9911-3a3dac7d28ab

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_458
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_459
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_460
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_461
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_462
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_463

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

lemma degreeUnionBranch62_457_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_457 [9,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_458
  · exact degreeUnionBranch62_459
  · exact degreeUnionBranch62_460
  · exact degreeUnionBranch62_461
  · exact degreeUnionBranch62_462
  · exact degreeUnionBranch62_463

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_457_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_457_oai
