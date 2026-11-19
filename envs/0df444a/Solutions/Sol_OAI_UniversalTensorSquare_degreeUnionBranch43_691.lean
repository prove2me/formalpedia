-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_691
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:35:56.612363+00:00
-- url     : https://prove2.me/submissions/ce5f3b4b-a139-414d-bd65-08711eafce35

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

lemma degreeUnionBranch43_692 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 30 3 degreeUnionState43_692 [3,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_693 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 29 4 degreeUnionState43_693 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_694 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 28 5 degreeUnionState43_694 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_695 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 27 6 degreeUnionState43_695 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_696 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 26 7 degreeUnionState43_696 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_697 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 25 8 degreeUnionState43_697 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_698 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 24 9 degreeUnionState43_698 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_699 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 23 10 degreeUnionState43_699 [10,10] = true := by
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

lemma degreeUnionBranch43_691_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 33 10 degreeUnionState43_691 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 12*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_692
  · exact degreeUnionBranch43_693
  · exact degreeUnionBranch43_694
  · exact degreeUnionBranch43_695
  · exact degreeUnionBranch43_696
  · exact degreeUnionBranch43_697
  · exact degreeUnionBranch43_698
  · exact degreeUnionBranch43_699

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_691_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_691_oai
