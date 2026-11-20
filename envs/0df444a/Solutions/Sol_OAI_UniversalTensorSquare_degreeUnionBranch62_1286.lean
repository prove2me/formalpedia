-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1286
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:07:39.516444+00:00
-- url     : https://prove2.me/submissions/56faba97-a503-4ec0-a32d-3144089bf378

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1287
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1288
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1289
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1290
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1291
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1292
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1293

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

lemma degreeUnionBranch62_1286_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 9 degreeUnionState62_1286 [9,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1287
  · exact degreeUnionBranch62_1288
  · exact degreeUnionBranch62_1289
  · exact degreeUnionBranch62_1290
  · exact degreeUnionBranch62_1291
  · exact degreeUnionBranch62_1292
  · exact degreeUnionBranch62_1293

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1286_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1286_oai
