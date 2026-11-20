-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_474
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:37:58.074574+00:00
-- url     : https://prove2.me/submissions/5c03fdaa-3755-46b4-b9ec-df2e0fcb61ec

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_475
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_476

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

lemma degreeUnionBranch62_477 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 6 degreeUnionState62_477 [6,8,11,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_478 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 7 degreeUnionState62_478 [7,8,11,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_479 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 21 8 degreeUnionState62_479 [8,8,11,14] = true := by
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

lemma degreeUnionBranch62_474_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 8 degreeUnionState62_474 [8,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_475
  · exact degreeUnionBranch62_476
  · exact degreeUnionBranch62_477
  · exact degreeUnionBranch62_478
  · exact degreeUnionBranch62_479

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_474_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_474_oai
