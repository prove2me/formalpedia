-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_249
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:43:14.598078+00:00
-- url     : https://prove2.me/submissions/2480865a-8fb8-41cf-b6fd-36edf181f79c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_250
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_251
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_252
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_253
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_254
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_255

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

lemma degreeUnionBranch62_249_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_249 [9,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_250
  · exact degreeUnionBranch62_251
  · exact degreeUnionBranch62_252
  · exact degreeUnionBranch62_253
  · exact degreeUnionBranch62_254
  · exact degreeUnionBranch62_255

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_249_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_249_oai
