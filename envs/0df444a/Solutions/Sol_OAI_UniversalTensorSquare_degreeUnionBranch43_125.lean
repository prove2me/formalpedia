-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_125
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:15:08.523453+00:00
-- url     : https://prove2.me/submissions/04e50bfe-ef86-40b0-a38d-a00e26e0f60f

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

lemma degreeUnionBranch43_126 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 20 4 degreeUnionState43_126 [4,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_127 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 19 5 degreeUnionState43_127 [5,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_128 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 18 6 degreeUnionState43_128 [6,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_129 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 7 degreeUnionState43_129 [7,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_130 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 16 8 degreeUnionState43_130 [8,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_131 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 15 9 degreeUnionState43_131 [9,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_132 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 14 10 degreeUnionState43_132 [10,19] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_133 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 13 11 degreeUnionState43_133 [11,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_134 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 12 12 degreeUnionState43_134 [12,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_135 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 11 13 degreeUnionState43_135 [13,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_136 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 10 14 degreeUnionState43_136 [14,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_137 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 9 15 degreeUnionState43_137 [15,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_138 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 8 16 degreeUnionState43_138 [16,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_139 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 7 17 degreeUnionState43_139 [17,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_140 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 6 18 degreeUnionState43_140 [18,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_141 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 5 19 degreeUnionState43_141 [19,19] = true := by
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

lemma degreeUnionBranch43_125_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 24 19 degreeUnionState43_125 [19] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 19 at hb
  change 24 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_126
  · exact degreeUnionBranch43_127
  · exact degreeUnionBranch43_128
  · exact degreeUnionBranch43_129
  · exact degreeUnionBranch43_130
  · exact degreeUnionBranch43_131
  · exact degreeUnionBranch43_132
  · exact degreeUnionBranch43_133
  · exact degreeUnionBranch43_134
  · exact degreeUnionBranch43_135
  · exact degreeUnionBranch43_136
  · exact degreeUnionBranch43_137
  · exact degreeUnionBranch43_138
  · exact degreeUnionBranch43_139
  · exact degreeUnionBranch43_140
  · exact degreeUnionBranch43_141

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_125_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_125_oai
