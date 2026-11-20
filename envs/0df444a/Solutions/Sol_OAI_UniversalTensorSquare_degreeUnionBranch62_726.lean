-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_726
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:00:03.028999+00:00
-- url     : https://prove2.me/submissions/cf0e5e76-e7f0-4167-ae93-5c0879bf1ff1

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_727
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_728
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_729
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_730
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_731
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_737

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

lemma degreeUnionBranch62_726_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 9 degreeUnionState62_726 [9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 40 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_727
  · exact degreeUnionBranch62_728
  · exact degreeUnionBranch62_729
  · exact degreeUnionBranch62_730
  · exact degreeUnionBranch62_731
  · exact degreeUnionBranch62_737

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_726_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_726_oai
