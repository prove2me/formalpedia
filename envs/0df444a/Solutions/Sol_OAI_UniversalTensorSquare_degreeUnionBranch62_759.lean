-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_759
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:06:38.621399+00:00
-- url     : https://prove2.me/submissions/1a9ad9fc-b1a3-450a-b640-e1666165a02d

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_760
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_761
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_762
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_763
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_764
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_765

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

lemma degreeUnionBranch62_766 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 9 degreeUnionState62_766 [9,9,10,13] = true := by
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

lemma degreeUnionBranch62_759_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 9 degreeUnionState62_759 [9,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_760
  · exact degreeUnionBranch62_761
  · exact degreeUnionBranch62_762
  · exact degreeUnionBranch62_763
  · exact degreeUnionBranch62_764
  · exact degreeUnionBranch62_765
  · exact degreeUnionBranch62_766

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_759_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_759_oai
