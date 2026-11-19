-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_142
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:15:14.752966+00:00
-- url     : https://prove2.me/submissions/779a2faa-61e2-41e5-bd4a-5e75ac1b0a4f

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

lemma degreeUnionBranch43_143 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 19 4 degreeUnionState43_143 [4,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_144 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 18 5 degreeUnionState43_144 [5,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_145 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 6 degreeUnionState43_145 [6,20] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_146 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 16 7 degreeUnionState43_146 [7,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_147 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 15 8 degreeUnionState43_147 [8,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_148 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 14 9 degreeUnionState43_148 [9,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_149 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 13 10 degreeUnionState43_149 [10,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_150 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 12 11 degreeUnionState43_150 [11,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_151 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 11 12 degreeUnionState43_151 [12,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_152 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 10 13 degreeUnionState43_152 [13,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_153 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 9 14 degreeUnionState43_153 [14,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_154 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 8 15 degreeUnionState43_154 [15,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_155 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 7 16 degreeUnionState43_155 [16,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_156 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 6 17 degreeUnionState43_156 [17,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_157 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 5 18 degreeUnionState43_157 [18,20] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_158 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 4 19 degreeUnionState43_158 [19,20] = true := by
  decide +kernel

lemma degreeUnionBranch43_159 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 3 20 degreeUnionState43_159 [20,20] = true := by
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

lemma degreeUnionBranch43_142_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 20 degreeUnionState43_142 [20] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 20 at hb
  change 23 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_143
  · exact degreeUnionBranch43_144
  · exact degreeUnionBranch43_145
  · exact degreeUnionBranch43_146
  · exact degreeUnionBranch43_147
  · exact degreeUnionBranch43_148
  · exact degreeUnionBranch43_149
  · exact degreeUnionBranch43_150
  · exact degreeUnionBranch43_151
  · exact degreeUnionBranch43_152
  · exact degreeUnionBranch43_153
  · exact degreeUnionBranch43_154
  · exact degreeUnionBranch43_155
  · exact degreeUnionBranch43_156
  · exact degreeUnionBranch43_157
  · exact degreeUnionBranch43_158
  · exact degreeUnionBranch43_159

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_142_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_142_oai
