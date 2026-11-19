-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:11:56.881625+00:00
-- url     : https://prove2.me/submissions/38acbe12-6c59-4a79-bd43-395d3f05e281

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch24_27
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch24_48
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch24_6
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch24_71
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch24_72

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 24. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_0 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 0 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_1 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 1 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_2 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 2 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_3 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 3 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_4 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 4 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_5 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_70 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 9 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_73 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 12 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_74 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 13 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_75 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 14 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_76 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 15 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_77 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 16 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_78 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 17 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_79 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 18 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_80 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 19 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_81 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 20 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_82 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 21 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_83 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 22 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

lemma degreeUnionBranch24_84 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 23 24 23 degreeHalfRegions24 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 24. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck24_oai : ∀ h ≤ 23,
    checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) h 24 23 degreeHalfRegions24 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch24_0
  · exact degreeUnionBranch24_1
  · exact degreeUnionBranch24_2
  · exact degreeUnionBranch24_3
  · exact degreeUnionBranch24_4
  · exact degreeUnionBranch24_5
  · exact degreeUnionBranch24_6
  · exact degreeUnionBranch24_27
  · exact degreeUnionBranch24_48
  · exact degreeUnionBranch24_70
  · exact degreeUnionBranch24_71
  · exact degreeUnionBranch24_72
  · exact degreeUnionBranch24_73
  · exact degreeUnionBranch24_74
  · exact degreeUnionBranch24_75
  · exact degreeUnionBranch24_76
  · exact degreeUnionBranch24_77
  · exact degreeUnionBranch24_78
  · exact degreeUnionBranch24_79
  · exact degreeUnionBranch24_80
  · exact degreeUnionBranch24_81
  · exact degreeUnionBranch24_82
  · exact degreeUnionBranch24_83
  · exact degreeUnionBranch24_84

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck24_oai := @OAI.UniversalTensorSquare.degreeUnionCheck24_oai
