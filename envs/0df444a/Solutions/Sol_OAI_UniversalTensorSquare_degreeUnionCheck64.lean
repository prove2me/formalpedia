-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionCheck64
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:11:36.748444+00:00
-- url     : https://prove2.me/submissions/9840a80e-72c4-4392-9716-091e6c11edc9

import Mathlib
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_12
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_13
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_14
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_15
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_16
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_17
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_18
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_19
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_20
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_21
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_22
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_23
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_24
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_25
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_26
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_27
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_28
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_29
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_30
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_5
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_6
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_7
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_8
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch64_9

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 64. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck64_oai : ∀ h ≤ 30,
    checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) h 64 30 degreeHalfRegions64 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch64_0
  · exact degreeUnionBranch64_1
  · exact degreeUnionBranch64_2
  · exact degreeUnionBranch64_3
  · exact degreeUnionBranch64_4
  · exact degreeUnionBranch64_5
  · exact degreeUnionBranch64_6
  · exact degreeUnionBranch64_7
  · exact degreeUnionBranch64_8
  · exact degreeUnionBranch64_9
  · exact degreeUnionBranch64_10
  · exact degreeUnionBranch64_11
  · exact degreeUnionBranch64_12
  · exact degreeUnionBranch64_13
  · exact degreeUnionBranch64_14
  · exact degreeUnionBranch64_15
  · exact degreeUnionBranch64_16
  · exact degreeUnionBranch64_17
  · exact degreeUnionBranch64_18
  · exact degreeUnionBranch64_19
  · exact degreeUnionBranch64_20
  · exact degreeUnionBranch64_21
  · exact degreeUnionBranch64_22
  · exact degreeUnionBranch64_23
  · exact degreeUnionBranch64_24
  · exact degreeUnionBranch64_25
  · exact degreeUnionBranch64_26
  · exact degreeUnionBranch64_27
  · exact degreeUnionBranch64_28
  · exact degreeUnionBranch64_29
  · exact degreeUnionBranch64_30

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionCheck64_oai := @OAI.UniversalTensorSquare.degreeUnionCheck64_oai
