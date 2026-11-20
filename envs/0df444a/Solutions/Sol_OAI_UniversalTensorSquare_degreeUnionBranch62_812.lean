-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_812
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:39:23.500902+00:00
-- url     : https://prove2.me/submissions/96ec23d1-4534-4796-a30f-fa772808f37d

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_813
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_814
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_815
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_816
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_817

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_818 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 8 degreeUnionState62_818 [8,8,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

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

lemma degreeUnionBranch62_812_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 8 degreeUnionState62_812 [8,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_813
  · exact degreeUnionBranch62_814
  · exact degreeUnionBranch62_815
  · exact degreeUnionBranch62_816
  · exact degreeUnionBranch62_817
  · exact degreeUnionBranch62_818

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_812_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_812_oai
