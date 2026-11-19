-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_138
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:10.766713+00:00
-- url     : https://prove2.me/submissions/285ff742-4e1f-494d-8f91-c3df57bc4652

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

lemma degreeUnionBranch39_139 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 25 4 degreeUnionState39_139 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_140 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 24 5 degreeUnionState39_140 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_141 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 6 degreeUnionState39_141 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_142 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 22 7 degreeUnionState39_142 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_143 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 8 degreeUnionState39_143 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_144 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 20 9 degreeUnionState39_144 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_145 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 10 degreeUnionState39_145 [10,10] = true := by
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

lemma degreeUnionBranch39_138_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 29 10 degreeUnionState39_138 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_139
  · exact degreeUnionBranch39_140
  · exact degreeUnionBranch39_141
  · exact degreeUnionBranch39_142
  · exact degreeUnionBranch39_143
  · exact degreeUnionBranch39_144
  · exact degreeUnionBranch39_145

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_138_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_138_oai
