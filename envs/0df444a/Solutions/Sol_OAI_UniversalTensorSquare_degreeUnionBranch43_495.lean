-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_495
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:12:56.004581+00:00
-- url     : https://prove2.me/submissions/32c9e2dc-5594-4f81-a004-30a93109d100

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

lemma degreeUnionBranch43_496 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 21 3 degreeUnionState43_496 [3,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_497 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 4 degreeUnionState43_497 [4,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_498 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 5 degreeUnionState43_498 [5,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_499 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 6 degreeUnionState43_499 [6,19] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_500 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 7 degreeUnionState43_500 [7,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_501 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 8 degreeUnionState43_501 [8,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_502 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 9 degreeUnionState43_502 [9,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_503 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 14 10 degreeUnionState43_503 [10,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_504 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 13 11 degreeUnionState43_504 [11,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_505 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 12 12 degreeUnionState43_505 [12,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_506 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 11 13 degreeUnionState43_506 [13,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_507 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 10 14 degreeUnionState43_507 [14,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_508 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 9 15 degreeUnionState43_508 [15,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_509 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 8 16 degreeUnionState43_509 [16,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_510 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 7 17 degreeUnionState43_510 [17,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_511 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 6 18 degreeUnionState43_511 [18,19] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_512 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 5 19 degreeUnionState43_512 [19,19] = true := by
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

lemma degreeUnionBranch43_495_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 24 19 degreeUnionState43_495 [19] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 19 at hb
  change 24 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_496
  · exact degreeUnionBranch43_497
  · exact degreeUnionBranch43_498
  · exact degreeUnionBranch43_499
  · exact degreeUnionBranch43_500
  · exact degreeUnionBranch43_501
  · exact degreeUnionBranch43_502
  · exact degreeUnionBranch43_503
  · exact degreeUnionBranch43_504
  · exact degreeUnionBranch43_505
  · exact degreeUnionBranch43_506
  · exact degreeUnionBranch43_507
  · exact degreeUnionBranch43_508
  · exact degreeUnionBranch43_509
  · exact degreeUnionBranch43_510
  · exact degreeUnionBranch43_511
  · exact degreeUnionBranch43_512

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_495_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_495_oai
