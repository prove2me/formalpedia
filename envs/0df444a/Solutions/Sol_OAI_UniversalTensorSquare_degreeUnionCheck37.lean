-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:14.865993+00:00
-- url     : https://prove2.me/submissions/5602ebc9-08b1-497e-8429-b984437bbbd4

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch37_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch37_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch37_12
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch37_13
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch37_14
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch37_15

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 37. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch37_0 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 0 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_1 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 1 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_2 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 2 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_3 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 3 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_4 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 4 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_5 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 5 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_6 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 6 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_7 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 7 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_8 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 8 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_9 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 9 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch37_16 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 16 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

lemma degreeUnionBranch37_17 : checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) 17 37 17 degreeHalfRegions37 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 37. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck37_oai : ∀ h ≤ 17,
    checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) h 37 17 degreeHalfRegions37 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch37_0
  · exact degreeUnionBranch37_1
  · exact degreeUnionBranch37_2
  · exact degreeUnionBranch37_3
  · exact degreeUnionBranch37_4
  · exact degreeUnionBranch37_5
  · exact degreeUnionBranch37_6
  · exact degreeUnionBranch37_7
  · exact degreeUnionBranch37_8
  · exact degreeUnionBranch37_9
  · exact degreeUnionBranch37_10
  · exact degreeUnionBranch37_11
  · exact degreeUnionBranch37_12
  · exact degreeUnionBranch37_13
  · exact degreeUnionBranch37_14
  · exact degreeUnionBranch37_15
  · exact degreeUnionBranch37_16
  · exact degreeUnionBranch37_17

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck37_oai := @OAI.UniversalTensorSquare.degreeUnionCheck37_oai
