-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_643
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:27:27.638773+00:00
-- url     : https://prove2.me/submissions/4f6b587c-0c84-4447-8634-630c2f03ccee

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

lemma degreeUnionBranch43_644 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 28 3 degreeUnionState43_644 [3,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_645 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 27 4 degreeUnionState43_645 [4,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_646 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 26 5 degreeUnionState43_646 [5,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_647 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 25 6 degreeUnionState43_647 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_648 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 24 7 degreeUnionState43_648 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_649 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 23 8 degreeUnionState43_649 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_650 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 22 9 degreeUnionState43_650 [9,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_651 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 21 10 degreeUnionState43_651 [10,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_652 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 20 11 degreeUnionState43_652 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_653 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 19 12 degreeUnionState43_653 [12,12] = true := by
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

lemma degreeUnionBranch43_643_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 31 12 degreeUnionState43_643 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_644
  · exact degreeUnionBranch43_645
  · exact degreeUnionBranch43_646
  · exact degreeUnionBranch43_647
  · exact degreeUnionBranch43_648
  · exact degreeUnionBranch43_649
  · exact degreeUnionBranch43_650
  · exact degreeUnionBranch43_651
  · exact degreeUnionBranch43_652
  · exact degreeUnionBranch43_653

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_643_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_643_oai
