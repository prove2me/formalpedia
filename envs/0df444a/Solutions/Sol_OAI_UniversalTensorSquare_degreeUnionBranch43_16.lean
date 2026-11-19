-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:15:20.454782+00:00
-- url     : https://prove2.me/submissions/980c771a-99a7-4e99-ac57-72e93f566bc0

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

lemma degreeUnionBranch43_17 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 29 5 degreeUnionState43_17 [5,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_18 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 28 6 degreeUnionState43_18 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_19 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 27 7 degreeUnionState43_19 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_20 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 26 8 degreeUnionState43_20 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_21 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 25 9 degreeUnionState43_21 [9,9] = true := by
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

lemma degreeUnionBranch43_16_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 34 9 degreeUnionState43_16 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_17
  · exact degreeUnionBranch43_18
  · exact degreeUnionBranch43_19
  · exact degreeUnionBranch43_20
  · exact degreeUnionBranch43_21

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_16_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_16_oai
