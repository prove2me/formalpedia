-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:08.869204+00:00
-- url     : https://prove2.me/submissions/532e9368-5017-4f7c-b823-e464b2a974af

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_102
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_52
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_8

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_0 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 0 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_1 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 1 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_2 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 2 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_3 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 3 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_4 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 4 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_5 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 5 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_6 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_7 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_155 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 11 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_156 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 12 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_157 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 13 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_158 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 14 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

lemma degreeUnionBranch35_159 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 15 35 34 degreeHalfRegions35 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck35_oai : ∀ h ≤ 15,
    checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) h 35 34 degreeHalfRegions35 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch35_0
  · exact degreeUnionBranch35_1
  · exact degreeUnionBranch35_2
  · exact degreeUnionBranch35_3
  · exact degreeUnionBranch35_4
  · exact degreeUnionBranch35_5
  · exact degreeUnionBranch35_6
  · exact degreeUnionBranch35_7
  · exact degreeUnionBranch35_8
  · exact degreeUnionBranch35_52
  · exact degreeUnionBranch35_102
  · exact degreeUnionBranch35_155
  · exact degreeUnionBranch35_156
  · exact degreeUnionBranch35_157
  · exact degreeUnionBranch35_158
  · exact degreeUnionBranch35_159

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck35_oai := @OAI.UniversalTensorSquare.degreeUnionCheck35_oai
