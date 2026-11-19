-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:02.836576+00:00
-- url     : https://prove2.me/submissions/97e2c103-9784-4177-88bd-4728a6b0b09e

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_30
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_53
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_7
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_77
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_78
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_79
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_80
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_81
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_82
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_83
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_84
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_85
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_86
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_87
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_88
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_89
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_90
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_91
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch26_92

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 26. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_0 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 0 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

lemma degreeUnionBranch26_1 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 1 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

lemma degreeUnionBranch26_2 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 2 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

lemma degreeUnionBranch26_3 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 3 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

lemma degreeUnionBranch26_4 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 4 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

lemma degreeUnionBranch26_5 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 5 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

lemma degreeUnionBranch26_6 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 26 25 degreeHalfRegions26 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 26. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck26_oai : ∀ h ≤ 25,
    checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) h 26 25 degreeHalfRegions26 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch26_0
  · exact degreeUnionBranch26_1
  · exact degreeUnionBranch26_2
  · exact degreeUnionBranch26_3
  · exact degreeUnionBranch26_4
  · exact degreeUnionBranch26_5
  · exact degreeUnionBranch26_6
  · exact degreeUnionBranch26_7
  · exact degreeUnionBranch26_30
  · exact degreeUnionBranch26_53
  · exact degreeUnionBranch26_77
  · exact degreeUnionBranch26_78
  · exact degreeUnionBranch26_79
  · exact degreeUnionBranch26_80
  · exact degreeUnionBranch26_81
  · exact degreeUnionBranch26_82
  · exact degreeUnionBranch26_83
  · exact degreeUnionBranch26_84
  · exact degreeUnionBranch26_85
  · exact degreeUnionBranch26_86
  · exact degreeUnionBranch26_87
  · exact degreeUnionBranch26_88
  · exact degreeUnionBranch26_89
  · exact degreeUnionBranch26_90
  · exact degreeUnionBranch26_91
  · exact degreeUnionBranch26_92

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck26_oai := @OAI.UniversalTensorSquare.degreeUnionCheck26_oai
