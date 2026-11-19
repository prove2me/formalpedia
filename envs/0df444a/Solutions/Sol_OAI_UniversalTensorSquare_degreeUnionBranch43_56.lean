-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_56
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:20:55.898074+00:00
-- url     : https://prove2.me/submissions/2285308a-e161-4849-8096-b3e8d964f8cd

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_57
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_58
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_59
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_60
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_61
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_62
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_63
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_64
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_65
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_66

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

lemma degreeUnionBranch43_56_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 29 14 degreeUnionState43_56 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 29 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_57
  · exact degreeUnionBranch43_58
  · exact degreeUnionBranch43_59
  · exact degreeUnionBranch43_60
  · exact degreeUnionBranch43_61
  · exact degreeUnionBranch43_62
  · exact degreeUnionBranch43_63
  · exact degreeUnionBranch43_64
  · exact degreeUnionBranch43_65
  · exact degreeUnionBranch43_66

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_56_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_56_oai
