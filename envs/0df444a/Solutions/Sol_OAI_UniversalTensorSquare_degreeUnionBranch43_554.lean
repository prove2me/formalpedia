-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_554
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:20:50.102158+00:00
-- url     : https://prove2.me/submissions/28355bf6-ae12-4420-b905-044798d0df9c

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

lemma degreeUnionBranch43_555 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 29 4 degreeUnionState43_555 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_556 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 28 5 degreeUnionState43_556 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_557 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 27 6 degreeUnionState43_557 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_558 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 26 7 degreeUnionState43_558 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_559 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 25 8 degreeUnionState43_559 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_560 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 24 9 degreeUnionState43_560 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_561 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 23 10 degreeUnionState43_561 [10,10] = true := by
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

lemma degreeUnionBranch43_554_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 33 10 degreeUnionState43_554 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_555
  · exact degreeUnionBranch43_556
  · exact degreeUnionBranch43_557
  · exact degreeUnionBranch43_558
  · exact degreeUnionBranch43_559
  · exact degreeUnionBranch43_560
  · exact degreeUnionBranch43_561

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_554_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_554_oai
