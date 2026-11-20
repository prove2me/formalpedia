-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_696
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:44:49.377176+00:00
-- url     : https://prove2.me/submissions/29e02603-5055-4b9e-80b9-77b6c2fc38b4

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_697
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_698
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_699
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_700
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_701
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_702
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_703

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

lemma degreeUnionBranch62_696_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 9 degreeUnionState62_696 [9,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_697
  · exact degreeUnionBranch62_698
  · exact degreeUnionBranch62_699
  · exact degreeUnionBranch62_700
  · exact degreeUnionBranch62_701
  · exact degreeUnionBranch62_702
  · exact degreeUnionBranch62_703

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_696_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_696_oai
