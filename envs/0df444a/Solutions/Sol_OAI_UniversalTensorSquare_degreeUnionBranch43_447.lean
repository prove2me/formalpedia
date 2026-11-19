-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_447
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:11:28.827806+00:00
-- url     : https://prove2.me/submissions/798a59ff-9f2d-4b75-8278-9a64a103ddad

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_448
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_455
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_456
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_457
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_458
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_459
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_460
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_461

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_449 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 23 4 degreeUnionState43_449 [4,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_450 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 5 degreeUnionState43_450 [5,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_451 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 21 6 degreeUnionState43_451 [6,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_452 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 7 degreeUnionState43_452 [7,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_453 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 8 degreeUnionState43_453 [8,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_454 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 9 degreeUnionState43_454 [9,16] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_447_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 27 16 degreeUnionState43_447 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 27 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_448
  · exact degreeUnionBranch43_449
  · exact degreeUnionBranch43_450
  · exact degreeUnionBranch43_451
  · exact degreeUnionBranch43_452
  · exact degreeUnionBranch43_453
  · exact degreeUnionBranch43_454
  · exact degreeUnionBranch43_455
  · exact degreeUnionBranch43_456
  · exact degreeUnionBranch43_457
  · exact degreeUnionBranch43_458
  · exact degreeUnionBranch43_459
  · exact degreeUnionBranch43_460
  · exact degreeUnionBranch43_461

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_447_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_447_oai
