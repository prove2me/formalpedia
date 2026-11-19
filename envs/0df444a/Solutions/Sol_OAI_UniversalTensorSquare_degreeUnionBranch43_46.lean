-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:12:11.662881+00:00
-- url     : https://prove2.me/submissions/e0d91b27-d754-4a73-bc55-64712cb6579a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_47
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_48
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_49
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_50
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_51
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_52
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_53
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_54
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_55

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_46_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 30 13 degreeUnionState43_46 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 30 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_47
  · exact degreeUnionBranch43_48
  · exact degreeUnionBranch43_49
  · exact degreeUnionBranch43_50
  · exact degreeUnionBranch43_51
  · exact degreeUnionBranch43_52
  · exact degreeUnionBranch43_53
  · exact degreeUnionBranch43_54
  · exact degreeUnionBranch43_55

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_46_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_46_oai
