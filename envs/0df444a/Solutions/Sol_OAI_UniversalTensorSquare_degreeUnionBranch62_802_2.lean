-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_802
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:45:11.637194+00:00
-- url     : https://prove2.me/submissions/57dead0a-61d1-4910-a815-5ef3182e6d71

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_803
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_804
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_805
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_806
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_812
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_820
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_821
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_822

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

lemma degreeUnionBranch62_819 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 9 degreeUnionState62_819 [9,12,13] = true := by
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

lemma degreeUnionBranch62_802_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 37 12 degreeUnionState62_802 [12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 37 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_803
  · exact degreeUnionBranch62_804
  · exact degreeUnionBranch62_805
  · exact degreeUnionBranch62_806
  · exact degreeUnionBranch62_812
  · exact degreeUnionBranch62_819
  · exact degreeUnionBranch62_820
  · exact degreeUnionBranch62_821
  · exact degreeUnionBranch62_822

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_802_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_802_oai
