-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_369
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:37:42.965768+00:00
-- url     : https://prove2.me/submissions/bc2436af-0a67-4614-a9ae-df5bfa34dde0

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_370
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_371
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_372
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_373

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

lemma degreeUnionBranch62_374 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 21 8 degreeUnionState62_374 [8,8,12,13] = true := by
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

lemma degreeUnionBranch62_369_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 8 degreeUnionState62_369 [8,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_370
  · exact degreeUnionBranch62_371
  · exact degreeUnionBranch62_372
  · exact degreeUnionBranch62_373
  · exact degreeUnionBranch62_374

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_369_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_369_oai
