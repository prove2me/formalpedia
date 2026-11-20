-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_122
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:42:54.227241+00:00
-- url     : https://prove2.me/submissions/a4d65562-b0c6-4bd6-a29c-1536244b0af6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_123
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_124
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_125
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_126
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_127
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_128
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_129
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_130

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

lemma degreeUnionBranch62_122_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 11 degreeUnionState62_122 [11,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_123
  · exact degreeUnionBranch62_124
  · exact degreeUnionBranch62_125
  · exact degreeUnionBranch62_126
  · exact degreeUnionBranch62_127
  · exact degreeUnionBranch62_128
  · exact degreeUnionBranch62_129
  · exact degreeUnionBranch62_130

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_122_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_122_oai
