-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_962
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:48:31.954484+00:00
-- url     : https://prove2.me/submissions/e3364a59-9791-43a0-9668-4b7c9c185995

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_963
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_964
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_965
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_966
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_967
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_968
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_969
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_977

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

lemma degreeUnionBranch62_962_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 51 11 degreeUnionState62_962 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 51 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_963
  · exact degreeUnionBranch62_964
  · exact degreeUnionBranch62_965
  · exact degreeUnionBranch62_966
  · exact degreeUnionBranch62_967
  · exact degreeUnionBranch62_968
  · exact degreeUnionBranch62_969
  · exact degreeUnionBranch62_977

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_962_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_962_oai
