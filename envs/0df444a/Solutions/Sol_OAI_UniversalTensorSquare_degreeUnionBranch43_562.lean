-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_562
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:21:01.846081+00:00
-- url     : https://prove2.me/submissions/3d31ee1a-85b1-4f62-bd31-1f4f2ea09d2a

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

lemma degreeUnionBranch43_563 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 28 4 degreeUnionState43_563 [4,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_564 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 27 5 degreeUnionState43_564 [5,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_565 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 26 6 degreeUnionState43_565 [6,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_566 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 25 7 degreeUnionState43_566 [7,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_567 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 24 8 degreeUnionState43_567 [8,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_568 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 23 9 degreeUnionState43_568 [9,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_569 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 22 10 degreeUnionState43_569 [10,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_570 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 21 11 degreeUnionState43_570 [11,11] = true := by
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

lemma degreeUnionBranch43_562_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 32 11 degreeUnionState43_562 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_563
  · exact degreeUnionBranch43_564
  · exact degreeUnionBranch43_565
  · exact degreeUnionBranch43_566
  · exact degreeUnionBranch43_567
  · exact degreeUnionBranch43_568
  · exact degreeUnionBranch43_569
  · exact degreeUnionBranch43_570

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_562_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_562_oai
