-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_155
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:22.343412+00:00
-- url     : https://prove2.me/submissions/cf636946-6eed-43cd-a3eb-e33a82c13583

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

lemma degreeUnionBranch39_156 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 4 degreeUnionState39_156 [4,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_157 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 22 5 degreeUnionState39_157 [5,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_158 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 6 degreeUnionState39_158 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_159 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 20 7 degreeUnionState39_159 [7,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_160 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 8 degreeUnionState39_160 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_161 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 18 9 degreeUnionState39_161 [9,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_162 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 17 10 degreeUnionState39_162 [10,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_163 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 16 11 degreeUnionState39_163 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_164 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 15 12 degreeUnionState39_164 [12,12] = true := by
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

lemma degreeUnionBranch39_155_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 27 12 degreeUnionState39_155 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_156
  · exact degreeUnionBranch39_157
  · exact degreeUnionBranch39_158
  · exact degreeUnionBranch39_159
  · exact degreeUnionBranch39_160
  · exact degreeUnionBranch39_161
  · exact degreeUnionBranch39_162
  · exact degreeUnionBranch39_163
  · exact degreeUnionBranch39_164

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_155_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_155_oai
