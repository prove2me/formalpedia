-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_877
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:18:51.888931+00:00
-- url     : https://prove2.me/submissions/5c46f269-38ea-4967-a7ca-fabe27d94f17

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_878
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_879
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_880
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_881
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_886
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_893
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_901

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

lemma degreeUnionBranch62_877_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 38 10 degreeUnionState62_877 [10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 38 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_878
  · exact degreeUnionBranch62_879
  · exact degreeUnionBranch62_880
  · exact degreeUnionBranch62_881
  · exact degreeUnionBranch62_886
  · exact degreeUnionBranch62_893
  · exact degreeUnionBranch62_901

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_877_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_877_oai
