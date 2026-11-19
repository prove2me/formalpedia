-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_462
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:12:28.493512+00:00
-- url     : https://prove2.me/submissions/7e7dea26-4058-4fac-ab1f-6b7d98ac228c

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

lemma degreeUnionBranch43_463 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 23 3 degreeUnionState43_463 [3,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_464 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 4 degreeUnionState43_464 [4,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_465 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 21 5 degreeUnionState43_465 [5,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_466 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 6 degreeUnionState43_466 [6,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_467 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 7 degreeUnionState43_467 [7,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_468 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 8 degreeUnionState43_468 [8,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_469 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 9 degreeUnionState43_469 [9,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_470 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 10 degreeUnionState43_470 [10,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_471 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 11 degreeUnionState43_471 [11,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_472 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 14 12 degreeUnionState43_472 [12,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_473 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 13 13 degreeUnionState43_473 [13,17] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_474 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 12 14 degreeUnionState43_474 [14,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_475 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 11 15 degreeUnionState43_475 [15,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_476 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 10 16 degreeUnionState43_476 [16,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_477 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 9 17 degreeUnionState43_477 [17,17] = true := by
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

lemma degreeUnionBranch43_462_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 26 17 degreeUnionState43_462 [17] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 17 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_463
  · exact degreeUnionBranch43_464
  · exact degreeUnionBranch43_465
  · exact degreeUnionBranch43_466
  · exact degreeUnionBranch43_467
  · exact degreeUnionBranch43_468
  · exact degreeUnionBranch43_469
  · exact degreeUnionBranch43_470
  · exact degreeUnionBranch43_471
  · exact degreeUnionBranch43_472
  · exact degreeUnionBranch43_473
  · exact degreeUnionBranch43_474
  · exact degreeUnionBranch43_475
  · exact degreeUnionBranch43_476
  · exact degreeUnionBranch43_477

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_462_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_462_oai
