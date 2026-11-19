-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_478
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:12:39.662003+00:00
-- url     : https://prove2.me/submissions/f451495a-4114-4aab-9a90-492a565ee468

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

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

lemma degreeUnionBranch43_479 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 3 degreeUnionState43_479 [3,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_480 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 21 4 degreeUnionState43_480 [4,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_481 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 5 degreeUnionState43_481 [5,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_482 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 6 degreeUnionState43_482 [6,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_483 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 7 degreeUnionState43_483 [7,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_484 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 8 degreeUnionState43_484 [8,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_485 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 9 degreeUnionState43_485 [9,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_486 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 10 degreeUnionState43_486 [10,18] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_487 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 14 11 degreeUnionState43_487 [11,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_488 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 13 12 degreeUnionState43_488 [12,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_489 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 12 13 degreeUnionState43_489 [13,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_490 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 11 14 degreeUnionState43_490 [14,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_491 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 10 15 degreeUnionState43_491 [15,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_492 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 9 16 degreeUnionState43_492 [16,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_493 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 8 17 degreeUnionState43_493 [17,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_494 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 7 18 degreeUnionState43_494 [18,18] = true := by
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

lemma degreeUnionBranch43_478_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 25 18 degreeUnionState43_478 [18] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 18 at hb
  change 25 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_479
  · exact degreeUnionBranch43_480
  · exact degreeUnionBranch43_481
  · exact degreeUnionBranch43_482
  · exact degreeUnionBranch43_483
  · exact degreeUnionBranch43_484
  · exact degreeUnionBranch43_485
  · exact degreeUnionBranch43_486
  · exact degreeUnionBranch43_487
  · exact degreeUnionBranch43_488
  · exact degreeUnionBranch43_489
  · exact degreeUnionBranch43_490
  · exact degreeUnionBranch43_491
  · exact degreeUnionBranch43_492
  · exact degreeUnionBranch43_493
  · exact degreeUnionBranch43_494

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_478_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_478_oai
