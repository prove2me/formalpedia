-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_165
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:28.257265+00:00
-- url     : https://prove2.me/submissions/d5435611-2f25-4162-a1fc-f7a00586a939

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

lemma degreeUnionBranch39_166 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 22 4 degreeUnionState39_166 [4,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_167 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 5 degreeUnionState39_167 [5,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_168 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 20 6 degreeUnionState39_168 [6,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_169 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 7 degreeUnionState39_169 [7,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_170 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 18 8 degreeUnionState39_170 [8,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_171 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 17 9 degreeUnionState39_171 [9,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_172 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 16 10 degreeUnionState39_172 [10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_173 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 15 11 degreeUnionState39_173 [11,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_174 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 14 12 degreeUnionState39_174 [12,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_175 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 13 13 degreeUnionState39_175 [13,13] = true := by
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

lemma degreeUnionBranch39_165_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 26 13 degreeUnionState39_165 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_166
  · exact degreeUnionBranch39_167
  · exact degreeUnionBranch39_168
  · exact degreeUnionBranch39_169
  · exact degreeUnionBranch39_170
  · exact degreeUnionBranch39_171
  · exact degreeUnionBranch39_172
  · exact degreeUnionBranch39_173
  · exact degreeUnionBranch39_174
  · exact degreeUnionBranch39_175

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_165_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_165_oai
