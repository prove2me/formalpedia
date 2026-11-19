-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck43
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:37:17.801281+00:00
-- url     : https://prove2.me/submissions/bb69f26a-e7dd-4a4f-b023-7ce1f1fc91ca

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_182
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_351
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_5
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_536
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_6
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_611
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_684
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_7
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_732
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_772
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_8
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_813
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_854
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_895
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_896
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_897
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_898
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_899
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_900

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck43_oai : ∀ h ≤ 23,
    checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) h 43 42 degreeHalfRegions43 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch43_0
  · exact degreeUnionBranch43_1
  · exact degreeUnionBranch43_2
  · exact degreeUnionBranch43_3
  · exact degreeUnionBranch43_4
  · exact degreeUnionBranch43_5
  · exact degreeUnionBranch43_6
  · exact degreeUnionBranch43_7
  · exact degreeUnionBranch43_8
  · exact degreeUnionBranch43_182
  · exact degreeUnionBranch43_351
  · exact degreeUnionBranch43_536
  · exact degreeUnionBranch43_611
  · exact degreeUnionBranch43_684
  · exact degreeUnionBranch43_732
  · exact degreeUnionBranch43_772
  · exact degreeUnionBranch43_813
  · exact degreeUnionBranch43_854
  · exact degreeUnionBranch43_895
  · exact degreeUnionBranch43_896
  · exact degreeUnionBranch43_897
  · exact degreeUnionBranch43_898
  · exact degreeUnionBranch43_899
  · exact degreeUnionBranch43_900

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck43_oai := @OAI.UniversalTensorSquare.degreeUnionCheck43_oai
