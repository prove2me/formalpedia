-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_483
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:43:21.549173+00:00
-- url     : https://prove2.me/submissions/d4d7de2b-18f4-4417-8e13-791b2f564a5f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_484
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_485
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_486
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_487
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_492
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_493
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_494
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_495
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_496

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

lemma degreeUnionBranch62_483_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 12 degreeUnionState62_483 [12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 36 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_484
  · exact degreeUnionBranch62_485
  · exact degreeUnionBranch62_486
  · exact degreeUnionBranch62_487
  · exact degreeUnionBranch62_492
  · exact degreeUnionBranch62_493
  · exact degreeUnionBranch62_494
  · exact degreeUnionBranch62_495
  · exact degreeUnionBranch62_496

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_483_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_483_oai
