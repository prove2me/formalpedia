-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_689
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:43:21.780456+00:00
-- url     : https://prove2.me/submissions/0e11ea7d-6d20-4341-8f1f-6a47bb796934

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_690
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_691
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_692
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_693
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_694
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_695

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

lemma degreeUnionBranch62_689_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 8 degreeUnionState62_689 [8,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_690
  · exact degreeUnionBranch62_691
  · exact degreeUnionBranch62_692
  · exact degreeUnionBranch62_693
  · exact degreeUnionBranch62_694
  · exact degreeUnionBranch62_695

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_689_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_689_oai
