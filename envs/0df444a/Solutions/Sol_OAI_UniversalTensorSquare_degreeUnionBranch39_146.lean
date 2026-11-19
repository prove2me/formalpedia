-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_146
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:16.553072+00:00
-- url     : https://prove2.me/submissions/1493373e-2e81-40c3-9b96-b7c26e3e650f

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

lemma degreeUnionBranch39_147 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 24 4 degreeUnionState39_147 [4,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_148 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 5 degreeUnionState39_148 [5,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_149 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 22 6 degreeUnionState39_149 [6,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_150 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 7 degreeUnionState39_150 [7,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_151 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 20 8 degreeUnionState39_151 [8,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_152 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 9 degreeUnionState39_152 [9,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_153 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 18 10 degreeUnionState39_153 [10,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_154 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 17 11 degreeUnionState39_154 [11,11] = true := by
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

lemma degreeUnionBranch39_146_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 28 11 degreeUnionState39_146 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 28 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_147
  · exact degreeUnionBranch39_148
  · exact degreeUnionBranch39_149
  · exact degreeUnionBranch39_150
  · exact degreeUnionBranch39_151
  · exact degreeUnionBranch39_152
  · exact degreeUnionBranch39_153
  · exact degreeUnionBranch39_154

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_146_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_146_oai
