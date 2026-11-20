-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_1059
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:42:32.721197+00:00
-- url     : https://prove2.me/submissions/8cc3ebdd-2e66-4dcd-abf9-79b2c91891f8

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1060
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1061
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1062
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1063
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1064
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1065
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1066
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1067

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

lemma degreeUnionBranch62_1059_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 10 degreeUnionState62_1059 [10,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1060
  · exact degreeUnionBranch62_1061
  · exact degreeUnionBranch62_1062
  · exact degreeUnionBranch62_1063
  · exact degreeUnionBranch62_1064
  · exact degreeUnionBranch62_1065
  · exact degreeUnionBranch62_1066
  · exact degreeUnionBranch62_1067

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1059_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1059_oai
