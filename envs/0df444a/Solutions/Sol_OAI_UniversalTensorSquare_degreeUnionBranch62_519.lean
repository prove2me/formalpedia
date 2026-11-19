-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_519
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:02:27.79691+00:00
-- url     : https://prove2.me/submissions/54c93b0f-e998-4532-866e-8f09d07ec49b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

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

lemma degreeUnionBranch62_520 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 47 5 degreeUnionState62_520 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_521 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 46 6 degreeUnionState62_521 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_522 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 45 7 degreeUnionState62_522 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_523 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 44 8 degreeUnionState62_523 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_524 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 43 9 degreeUnionState62_524 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_526 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 4 degreeUnionState62_526 [4,10,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_527 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 5 degreeUnionState62_527 [5,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_528 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 6 degreeUnionState62_528 [6,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_529 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 7 degreeUnionState62_529 [7,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_530 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 8 degreeUnionState62_530 [8,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_531 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 9 degreeUnionState62_531 [9,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_533 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 4 degreeUnionState62_533 [4,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_534 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 5 degreeUnionState62_534 [5,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_535 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 6 degreeUnionState62_535 [6,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_536 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 7 degreeUnionState62_536 [7,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_537 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 8 degreeUnionState62_537 [8,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_538 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 9 degreeUnionState62_538 [9,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_539 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 10 degreeUnionState62_539 [10,10,10,10] = true := by
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

lemma degreeUnionBranch62_532 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 10 degreeUnionState62_532 [10,10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_533
  · exact degreeUnionBranch62_534
  · exact degreeUnionBranch62_535
  · exact degreeUnionBranch62_536
  · exact degreeUnionBranch62_537
  · exact degreeUnionBranch62_538
  · exact degreeUnionBranch62_539

lemma degreeUnionBranch62_525 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 10 degreeUnionState62_525 [10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 42 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_526
  · exact degreeUnionBranch62_527
  · exact degreeUnionBranch62_528
  · exact degreeUnionBranch62_529
  · exact degreeUnionBranch62_530
  · exact degreeUnionBranch62_531
  · exact degreeUnionBranch62_532

lemma degreeUnionBranch62_519_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 52 10 degreeUnionState62_519 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 52 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_520
  · exact degreeUnionBranch62_521
  · exact degreeUnionBranch62_522
  · exact degreeUnionBranch62_523
  · exact degreeUnionBranch62_524
  · exact degreeUnionBranch62_525

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_519_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_519_oai
