-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck41
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:21.357308+00:00
-- url     : https://prove2.me/submissions/684298c6-ff75-4087-b2a4-51e7afc9e0aa

import Mathlib
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_12
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_13
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_14
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_15
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_16
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_17
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_18
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_19
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_20
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_21
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_8
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch41_9

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 41. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch41_0 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 0 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_1 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 1 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_2 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 2 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_3 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 3 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_4 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 4 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_5 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 5 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_6 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 6 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

lemma degreeUnionBranch41_7 : checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) 7 41 21 degreeHalfRegions41 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 41. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck41_oai : ∀ h ≤ 21,
    checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) h 41 21 degreeHalfRegions41 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch41_0
  · exact degreeUnionBranch41_1
  · exact degreeUnionBranch41_2
  · exact degreeUnionBranch41_3
  · exact degreeUnionBranch41_4
  · exact degreeUnionBranch41_5
  · exact degreeUnionBranch41_6
  · exact degreeUnionBranch41_7
  · exact degreeUnionBranch41_8
  · exact degreeUnionBranch41_9
  · exact degreeUnionBranch41_10
  · exact degreeUnionBranch41_11
  · exact degreeUnionBranch41_12
  · exact degreeUnionBranch41_13
  · exact degreeUnionBranch41_14
  · exact degreeUnionBranch41_15
  · exact degreeUnionBranch41_16
  · exact degreeUnionBranch41_17
  · exact degreeUnionBranch41_18
  · exact degreeUnionBranch41_19
  · exact degreeUnionBranch41_20
  · exact degreeUnionBranch41_21

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck41_oai := @OAI.UniversalTensorSquare.degreeUnionCheck41_oai
