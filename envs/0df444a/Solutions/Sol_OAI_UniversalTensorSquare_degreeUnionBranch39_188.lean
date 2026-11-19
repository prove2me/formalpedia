-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_188
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:45.431033+00:00
-- url     : https://prove2.me/submissions/cd0d28ab-0d57-45aa-8b4a-c73fab453a32

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

lemma degreeUnionBranch39_189 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 3 degreeUnionState39_189 [3,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_190 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 20 4 degreeUnionState39_190 [4,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_191 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 5 degreeUnionState39_191 [5,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_192 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 18 6 degreeUnionState39_192 [6,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_193 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 17 7 degreeUnionState39_193 [7,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_194 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 16 8 degreeUnionState39_194 [8,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_195 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 15 9 degreeUnionState39_195 [9,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_196 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 14 10 degreeUnionState39_196 [10,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_197 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 13 11 degreeUnionState39_197 [11,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_198 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 12 12 degreeUnionState39_198 [12,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_199 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 11 13 degreeUnionState39_199 [13,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_200 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 10 14 degreeUnionState39_200 [14,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_201 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 9 15 degreeUnionState39_201 [15,15] = true := by
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

lemma degreeUnionBranch39_188_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 24 15 degreeUnionState39_188 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 24 ≤ 8*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_189
  · exact degreeUnionBranch39_190
  · exact degreeUnionBranch39_191
  · exact degreeUnionBranch39_192
  · exact degreeUnionBranch39_193
  · exact degreeUnionBranch39_194
  · exact degreeUnionBranch39_195
  · exact degreeUnionBranch39_196
  · exact degreeUnionBranch39_197
  · exact degreeUnionBranch39_198
  · exact degreeUnionBranch39_199
  · exact degreeUnionBranch39_200
  · exact degreeUnionBranch39_201

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_188_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_188_oai
