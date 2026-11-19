-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_571
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:21:13.478322+00:00
-- url     : https://prove2.me/submissions/15d45e07-0c42-47f2-aff7-8b65a31aa8db

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

lemma degreeUnionBranch43_572 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 27 4 degreeUnionState43_572 [4,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_573 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 26 5 degreeUnionState43_573 [5,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_574 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 25 6 degreeUnionState43_574 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_575 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 24 7 degreeUnionState43_575 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_576 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 23 8 degreeUnionState43_576 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_577 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 22 9 degreeUnionState43_577 [9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_578 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 21 10 degreeUnionState43_578 [10,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_579 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 20 11 degreeUnionState43_579 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch43_580 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 19 12 degreeUnionState43_580 [12,12] = true := by
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

lemma degreeUnionBranch43_571_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 31 12 degreeUnionState43_571 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_572
  · exact degreeUnionBranch43_573
  · exact degreeUnionBranch43_574
  · exact degreeUnionBranch43_575
  · exact degreeUnionBranch43_576
  · exact degreeUnionBranch43_577
  · exact degreeUnionBranch43_578
  · exact degreeUnionBranch43_579
  · exact degreeUnionBranch43_580

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_571_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_571_oai
