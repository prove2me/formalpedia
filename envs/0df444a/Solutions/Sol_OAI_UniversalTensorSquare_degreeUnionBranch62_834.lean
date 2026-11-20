-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_834
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:42:45.148502+00:00
-- url     : https://prove2.me/submissions/7f653ff4-1dd0-4e0e-a262-ac4ab5f381e3

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_835
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_836
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_837
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_838
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_843
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_854
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_877
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_902
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_922
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_932
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_933

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

lemma degreeUnionBranch62_834_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 48 14 degreeUnionState62_834 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_835
  · exact degreeUnionBranch62_836
  · exact degreeUnionBranch62_837
  · exact degreeUnionBranch62_838
  · exact degreeUnionBranch62_843
  · exact degreeUnionBranch62_854
  · exact degreeUnionBranch62_877
  · exact degreeUnionBranch62_902
  · exact degreeUnionBranch62_922
  · exact degreeUnionBranch62_932
  · exact degreeUnionBranch62_933

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_834_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_834_oai
