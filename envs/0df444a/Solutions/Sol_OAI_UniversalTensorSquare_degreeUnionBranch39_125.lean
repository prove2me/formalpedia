-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_125
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:59.042296+00:00
-- url     : https://prove2.me/submissions/232c1354-d6c1-4dbf-b3f7-ced0a75cb26e

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_126 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 27 4 degreeUnionState39_126 [4,8] = true := by
  decide +kernel

lemma degreeUnionBranch39_127 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 26 5 degreeUnionState39_127 [5,8] = true := by
  decide +kernel

lemma degreeUnionBranch39_128 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 25 6 degreeUnionState39_128 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch39_129 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 24 7 degreeUnionState39_129 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch39_130 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 8 degreeUnionState39_130 [8,8] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_125_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 31 8 degreeUnionState39_125 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_126
  · exact degreeUnionBranch39_127
  · exact degreeUnionBranch39_128
  · exact degreeUnionBranch39_129
  · exact degreeUnionBranch39_130

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_125_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_125_oai
