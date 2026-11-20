-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_993
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:46:03.519476+00:00
-- url     : https://prove2.me/submissions/4a54bf5d-459d-476d-a86d-24ee55abe9f3

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1000
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1001
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1002
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_994
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_995
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_996
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_997
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_998
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_999

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

lemma degreeUnionBranch62_993_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 11 degreeUnionState62_993 [11,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 11 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_994
  · exact degreeUnionBranch62_995
  · exact degreeUnionBranch62_996
  · exact degreeUnionBranch62_997
  · exact degreeUnionBranch62_998
  · exact degreeUnionBranch62_999
  · exact degreeUnionBranch62_1000
  · exact degreeUnionBranch62_1001
  · exact degreeUnionBranch62_1002

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_993_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_993_oai
