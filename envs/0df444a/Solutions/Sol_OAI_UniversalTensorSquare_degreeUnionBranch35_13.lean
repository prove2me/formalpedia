-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:35:50.868887+00:00
-- url     : https://prove2.me/submissions/180db8f6-ae81-4439-a940-098a2679de42

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_14 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 22 4 degreeUnionState35_14 [4,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_15 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 21 5 degreeUnionState35_15 [5,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_16 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 20 6 degreeUnionState35_16 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_17 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 19 7 degreeUnionState35_17 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_18 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 18 8 degreeUnionState35_18 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_19 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 17 9 degreeUnionState35_19 [9,9] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_13_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 26 9 degreeUnionState35_13 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_14
  · exact degreeUnionBranch35_15
  · exact degreeUnionBranch35_16
  · exact degreeUnionBranch35_17
  · exact degreeUnionBranch35_18
  · exact degreeUnionBranch35_19

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_13_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_13_oai
