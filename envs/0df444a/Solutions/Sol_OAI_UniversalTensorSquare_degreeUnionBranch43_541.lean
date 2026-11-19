-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_541
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:20:32.809876+00:00
-- url     : https://prove2.me/submissions/d837ef6f-4a6a-4c34-ac56-87a5a8989631

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

lemma degreeUnionBranch43_542 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 31 4 degreeUnionState43_542 [4,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_543 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 30 5 degreeUnionState43_543 [5,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_544 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 29 6 degreeUnionState43_544 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_545 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 28 7 degreeUnionState43_545 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_546 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 27 8 degreeUnionState43_546 [8,8] = true := by
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

lemma degreeUnionBranch43_541_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 35 8 degreeUnionState43_541 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_542
  · exact degreeUnionBranch43_543
  · exact degreeUnionBranch43_544
  · exact degreeUnionBranch43_545
  · exact degreeUnionBranch43_546

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_541_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_541_oai
