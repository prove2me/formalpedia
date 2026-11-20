-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_863
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:02:00.239441+00:00
-- url     : https://prove2.me/submissions/5695df1f-2659-4418-aada-bca410f7ee73

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_864
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_865
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_866
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_867
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_868

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

lemma degreeUnionBranch62_863_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 8 degreeUnionState62_863 [8,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_864
  · exact degreeUnionBranch62_865
  · exact degreeUnionBranch62_866
  · exact degreeUnionBranch62_867
  · exact degreeUnionBranch62_868

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_863_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_863_oai
