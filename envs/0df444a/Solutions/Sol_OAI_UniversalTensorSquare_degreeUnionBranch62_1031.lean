-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1031
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:09:56.610843+00:00
-- url     : https://prove2.me/submissions/647336e0-f19a-416b-b111-4f98fe4fe86c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1032
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1033
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1034

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

lemma degreeUnionBranch62_1035 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 6 degreeUnionState62_1035 [6,9,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1036 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 7 degreeUnionState62_1036 [7,9,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1037 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 8 degreeUnionState62_1037 [8,9,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1038 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 9 degreeUnionState62_1038 [9,9,9,12] = true := by
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

lemma degreeUnionBranch62_1031_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 9 degreeUnionState62_1031 [9,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1032
  · exact degreeUnionBranch62_1033
  · exact degreeUnionBranch62_1034
  · exact degreeUnionBranch62_1035
  · exact degreeUnionBranch62_1036
  · exact degreeUnionBranch62_1037
  · exact degreeUnionBranch62_1038

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1031_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1031_oai
