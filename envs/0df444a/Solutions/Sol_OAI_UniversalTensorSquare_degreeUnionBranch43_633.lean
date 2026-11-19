-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_633
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:27:15.773517+00:00
-- url     : https://prove2.me/submissions/22493795-5b51-4731-b87e-2ad8e8d0541e

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

lemma degreeUnionBranch43_634 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 29 3 degreeUnionState43_634 [3,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_635 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 28 4 degreeUnionState43_635 [4,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_636 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 27 5 degreeUnionState43_636 [5,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_637 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 26 6 degreeUnionState43_637 [6,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_638 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 25 7 degreeUnionState43_638 [7,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_639 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 24 8 degreeUnionState43_639 [8,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_640 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 23 9 degreeUnionState43_640 [9,11] = true := by
  decide +kernel

lemma degreeUnionBranch43_641 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 22 10 degreeUnionState43_641 [10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_642 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 21 11 degreeUnionState43_642 [11,11] = true := by
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

lemma degreeUnionBranch43_633_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 32 11 degreeUnionState43_633 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_634
  · exact degreeUnionBranch43_635
  · exact degreeUnionBranch43_636
  · exact degreeUnionBranch43_637
  · exact degreeUnionBranch43_638
  · exact degreeUnionBranch43_639
  · exact degreeUnionBranch43_640
  · exact degreeUnionBranch43_641
  · exact degreeUnionBranch43_642

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_633_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_633_oai
