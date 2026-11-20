-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_823
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:45:18.952704+00:00
-- url     : https://prove2.me/submissions/344d8566-88e8-489a-857f-547aef24e2f2

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_824
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_825
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_826
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_827
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_828
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_829
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_830
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_831
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_832
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_833

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

lemma degreeUnionBranch62_823_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 13 degreeUnionState62_823 [13,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 36 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_824
  · exact degreeUnionBranch62_825
  · exact degreeUnionBranch62_826
  · exact degreeUnionBranch62_827
  · exact degreeUnionBranch62_828
  · exact degreeUnionBranch62_829
  · exact degreeUnionBranch62_830
  · exact degreeUnionBranch62_831
  · exact degreeUnionBranch62_832
  · exact degreeUnionBranch62_833

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_823_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_823_oai
