-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck62
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:27.352743+00:00
-- url     : https://prove2.me/submissions/0f76d96f-33d0-4937-a278-c98ec920ae34

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1337
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1338
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1339
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1340
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1341
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1342
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1343
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1344
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1345
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1346
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1347
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1348
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1349
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1350
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_513
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_62
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_948

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

lemma degreeUnionBranch62_0 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 0 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_1 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 1 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_2 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 2 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_3 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 3 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_4 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 4 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_5 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 5 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_6 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 6 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_7 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 7 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_8 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

lemma degreeUnionBranch62_9 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 62 28 degreeHalfRegions62 [] = true := by
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

lemma degreeUnionCheck62_oai : ∀ h ≤ 28,
    checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) h 62 28 degreeHalfRegions62 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch62_0
  · exact degreeUnionBranch62_1
  · exact degreeUnionBranch62_2
  · exact degreeUnionBranch62_3
  · exact degreeUnionBranch62_4
  · exact degreeUnionBranch62_5
  · exact degreeUnionBranch62_6
  · exact degreeUnionBranch62_7
  · exact degreeUnionBranch62_8
  · exact degreeUnionBranch62_9
  · exact degreeUnionBranch62_10
  · exact degreeUnionBranch62_11
  · exact degreeUnionBranch62_62
  · exact degreeUnionBranch62_513
  · exact degreeUnionBranch62_948
  · exact degreeUnionBranch62_1337
  · exact degreeUnionBranch62_1338
  · exact degreeUnionBranch62_1339
  · exact degreeUnionBranch62_1340
  · exact degreeUnionBranch62_1341
  · exact degreeUnionBranch62_1342
  · exact degreeUnionBranch62_1343
  · exact degreeUnionBranch62_1344
  · exact degreeUnionBranch62_1345
  · exact degreeUnionBranch62_1346
  · exact degreeUnionBranch62_1347
  · exact degreeUnionBranch62_1348
  · exact degreeUnionBranch62_1349
  · exact degreeUnionBranch62_1350

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck62_oai := @OAI.UniversalTensorSquare.degreeUnionCheck62_oai
