-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_355
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:49:37.079352+00:00
-- url     : https://prove2.me/submissions/ca2df60f-432f-4ab3-a039-8544132518c3

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

lemma degreeUnionBranch43_356 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 31 4 degreeUnionState43_356 [4,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_357 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 30 5 degreeUnionState43_357 [5,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_358 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 29 6 degreeUnionState43_358 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_359 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 28 7 degreeUnionState43_359 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_361 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 4 degreeUnionState43_361 [4,8,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_362 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 5 degreeUnionState43_362 [5,8,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_363 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 6 degreeUnionState43_363 [6,8,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_364 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 7 degreeUnionState43_364 [7,8,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_365 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 8 degreeUnionState43_365 [8,8,8] = true := by
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

lemma degreeUnionBranch43_360 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 27 8 degreeUnionState43_360 [8,8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_361
  · exact degreeUnionBranch43_362
  · exact degreeUnionBranch43_363
  · exact degreeUnionBranch43_364
  · exact degreeUnionBranch43_365

lemma degreeUnionBranch43_355_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 35 8 degreeUnionState43_355 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_356
  · exact degreeUnionBranch43_357
  · exact degreeUnionBranch43_358
  · exact degreeUnionBranch43_359
  · exact degreeUnionBranch43_360

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_355_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_355_oai
