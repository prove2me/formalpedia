-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_109
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:14:56.623207+00:00
-- url     : https://prove2.me/submissions/8f3cca6f-d01e-443c-bfbf-3bf055504e1c

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

lemma degreeUnionBranch43_110 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 4 degreeUnionState43_110 [4,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_111 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 20 5 degreeUnionState43_111 [5,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_112 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 19 6 degreeUnionState43_112 [6,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_113 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 18 7 degreeUnionState43_113 [7,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_114 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 8 degreeUnionState43_114 [8,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_115 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 16 9 degreeUnionState43_115 [9,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_116 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 15 10 degreeUnionState43_116 [10,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_117 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 14 11 degreeUnionState43_117 [11,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_118 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 13 12 degreeUnionState43_118 [12,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_119 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 12 13 degreeUnionState43_119 [13,18] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_120 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 11 14 degreeUnionState43_120 [14,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_121 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 10 15 degreeUnionState43_121 [15,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_122 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 9 16 degreeUnionState43_122 [16,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_123 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 8 17 degreeUnionState43_123 [17,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_124 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 7 18 degreeUnionState43_124 [18,18] = true := by
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

lemma degreeUnionBranch43_109_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 18 degreeUnionState43_109 [18] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 18 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_110
  · exact degreeUnionBranch43_111
  · exact degreeUnionBranch43_112
  · exact degreeUnionBranch43_113
  · exact degreeUnionBranch43_114
  · exact degreeUnionBranch43_115
  · exact degreeUnionBranch43_116
  · exact degreeUnionBranch43_117
  · exact degreeUnionBranch43_118
  · exact degreeUnionBranch43_119
  · exact degreeUnionBranch43_120
  · exact degreeUnionBranch43_121
  · exact degreeUnionBranch43_122
  · exact degreeUnionBranch43_123
  · exact degreeUnionBranch43_124

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_109_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_109_oai
