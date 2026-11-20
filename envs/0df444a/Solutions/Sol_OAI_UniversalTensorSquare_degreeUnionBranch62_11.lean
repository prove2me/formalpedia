-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:57:26.596209+00:00
-- url     : https://prove2.me/submissions/9d92a650-12eb-4b0e-aa8b-87836b721ca6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_18
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_27
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_37

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

lemma degreeUnionBranch62_12 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 56 6 degreeUnionState62_12 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_13 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 55 7 degreeUnionState62_13 [7] = true := by
  decide +kernel

lemma degreeUnionBranch62_14 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 54 8 degreeUnionState62_14 [8] = true := by
  decide +kernel

lemma degreeUnionBranch62_15 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 53 9 degreeUnionState62_15 [9] = true := by
  decide +kernel

lemma degreeUnionBranch62_16 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 52 10 degreeUnionState62_16 [10] = true := by
  decide +kernel

lemma degreeUnionBranch62_17 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 51 11 degreeUnionState62_17 [11] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_48 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 47 15 degreeUnionState62_48 [15] = true := by
  decide +kernel

lemma degreeUnionBranch62_49 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 46 16 degreeUnionState62_49 [16] = true := by
  decide +kernel

lemma degreeUnionBranch62_50 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 45 17 degreeUnionState62_50 [17] = true := by
  decide +kernel

lemma degreeUnionBranch62_51 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 44 18 degreeUnionState62_51 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_52 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 43 19 degreeUnionState62_52 [19] = true := by
  decide +kernel

lemma degreeUnionBranch62_53 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 42 20 degreeUnionState62_53 [20] = true := by
  decide +kernel

lemma degreeUnionBranch62_54 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 41 21 degreeUnionState62_54 [21] = true := by
  decide +kernel

lemma degreeUnionBranch62_55 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 40 22 degreeUnionState62_55 [22] = true := by
  decide +kernel

lemma degreeUnionBranch62_56 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 39 23 degreeUnionState62_56 [23] = true := by
  decide +kernel

lemma degreeUnionBranch62_57 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 24 degreeUnionState62_57 [24] = true := by
  decide +kernel

lemma degreeUnionBranch62_58 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 25 degreeUnionState62_58 [25] = true := by
  decide +kernel

lemma degreeUnionBranch62_59 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 26 degreeUnionState62_59 [26] = true := by
  decide +kernel

lemma degreeUnionBranch62_60 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 27 degreeUnionState62_60 [27] = true := by
  decide +kernel

lemma degreeUnionBranch62_61 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 28 degreeUnionState62_61 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SplitUnionRowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split Union Row Checker. -/

section

namespace UniversalTensorSquare

lemma checkRegionPrefixes_step (P : List ℕ → Bool) (k n upper : ℕ)
    (regions : List PrefixRegion) (pref : List ℕ)
    (hc : ∀ a, max 1 (n/(k+1)) ≤ a → a ≤ min n upper → n ≤ (k+1)*a →
      checkRegionPrefixes P k (n-a) a
        (nextRegions a (liveRegions (k+1) n upper regions)) (a::pref) = true) :
    checkRegionPrefixes P (k+1) n upper regions pref = true := by
  rw [checkRegionPrefixes]
  split_ifs with hnone
  · rfl
  · apply List.all_eq_true.mpr
    intro a ha
    have ha' := List.mem_range'_1.mp ha
    split_ifs with hn
    · apply hc a ha'.1 ?_ hn
      omega
    · rfl

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

lemma degreeUnionBranch62_11_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 11*a at hn
  have hlo : 6 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_12
  · exact degreeUnionBranch62_13
  · exact degreeUnionBranch62_14
  · exact degreeUnionBranch62_15
  · exact degreeUnionBranch62_16
  · exact degreeUnionBranch62_17
  · exact degreeUnionBranch62_18
  · exact degreeUnionBranch62_27
  · exact degreeUnionBranch62_37
  · exact degreeUnionBranch62_48
  · exact degreeUnionBranch62_49
  · exact degreeUnionBranch62_50
  · exact degreeUnionBranch62_51
  · exact degreeUnionBranch62_52
  · exact degreeUnionBranch62_53
  · exact degreeUnionBranch62_54
  · exact degreeUnionBranch62_55
  · exact degreeUnionBranch62_56
  · exact degreeUnionBranch62_57
  · exact degreeUnionBranch62_58
  · exact degreeUnionBranch62_59
  · exact degreeUnionBranch62_60
  · exact degreeUnionBranch62_61

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_11_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_11_oai
