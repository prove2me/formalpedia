-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_176
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:39.727686+00:00
-- url     : https://prove2.me/submissions/4e0d635d-b04b-41dd-972f-41abb23f4b8b

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

lemma degreeUnionBranch39_177 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 4 degreeUnionState39_177 [4,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_178 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 20 5 degreeUnionState39_178 [5,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_179 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 6 degreeUnionState39_179 [6,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_180 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 18 7 degreeUnionState39_180 [7,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_181 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 17 8 degreeUnionState39_181 [8,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_182 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 16 9 degreeUnionState39_182 [9,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_183 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 15 10 degreeUnionState39_183 [10,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_184 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 14 11 degreeUnionState39_184 [11,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_185 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 13 12 degreeUnionState39_185 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_186 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 12 13 degreeUnionState39_186 [13,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_187 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 11 14 degreeUnionState39_187 [14,14] = true := by
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

lemma degreeUnionBranch39_176_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 25 14 degreeUnionState39_176 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_177
  · exact degreeUnionBranch39_178
  · exact degreeUnionBranch39_179
  · exact degreeUnionBranch39_180
  · exact degreeUnionBranch39_181
  · exact degreeUnionBranch39_182
  · exact degreeUnionBranch39_183
  · exact degreeUnionBranch39_184
  · exact degreeUnionBranch39_185
  · exact degreeUnionBranch39_186
  · exact degreeUnionBranch39_187

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_176_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_176_oai
