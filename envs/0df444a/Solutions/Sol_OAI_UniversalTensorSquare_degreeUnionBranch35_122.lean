-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_122
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:35:45.117263+00:00
-- url     : https://prove2.me/submissions/52afa6d3-9439-41d4-a26c-375140d7bf1f

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

lemma degreeUnionBranch35_123 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 22 3 degreeUnionState35_123 [3,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_124 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 21 4 degreeUnionState35_124 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_125 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 20 5 degreeUnionState35_125 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_126 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 19 6 degreeUnionState35_126 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_127 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 18 7 degreeUnionState35_127 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_128 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 17 8 degreeUnionState35_128 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_129 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 16 9 degreeUnionState35_129 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_130 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 15 10 degreeUnionState35_130 [10,10] = true := by
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

lemma degreeUnionBranch35_122_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 25 10 degreeUnionState35_122 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 25 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_123
  · exact degreeUnionBranch35_124
  · exact degreeUnionBranch35_125
  · exact degreeUnionBranch35_126
  · exact degreeUnionBranch35_127
  · exact degreeUnionBranch35_128
  · exact degreeUnionBranch35_129
  · exact degreeUnionBranch35_130

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_122_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_122_oai
