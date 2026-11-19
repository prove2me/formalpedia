-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_617
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:26:53.244517+00:00
-- url     : https://prove2.me/submissions/eaa419fa-60ec-42e8-93e2-8ea7bbb3bdf9

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

lemma degreeUnionBranch43_618 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 30 4 degreeUnionState43_618 [4,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_619 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 29 5 degreeUnionState43_619 [5,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_620 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 28 6 degreeUnionState43_620 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_621 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 27 7 degreeUnionState43_621 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_622 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 26 8 degreeUnionState43_622 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_623 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 25 9 degreeUnionState43_623 [9,9] = true := by
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

lemma degreeUnionBranch43_617_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 34 9 degreeUnionState43_617 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_618
  · exact degreeUnionBranch43_619
  · exact degreeUnionBranch43_620
  · exact degreeUnionBranch43_621
  · exact degreeUnionBranch43_622
  · exact degreeUnionBranch43_623

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_617_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_617_oai
