-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_869
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:07:53.011528+00:00
-- url     : https://prove2.me/submissions/f5f4ed64-309b-45de-bb29-ceea06f8f524

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_870
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_871
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_872
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_873
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_874
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_875
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_876

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

lemma degreeUnionBranch62_869_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 9 degreeUnionState62_869 [9,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_870
  · exact degreeUnionBranch62_871
  · exact degreeUnionBranch62_872
  · exact degreeUnionBranch62_873
  · exact degreeUnionBranch62_874
  · exact degreeUnionBranch62_875
  · exact degreeUnionBranch62_876

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_869_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_869_oai
