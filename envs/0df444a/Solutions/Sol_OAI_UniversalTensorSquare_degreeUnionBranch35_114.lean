-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_114
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:35:32.915291+00:00
-- url     : https://prove2.me/submissions/0f2f132f-dd78-4b37-9f8d-a68261ef3ab0

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_115 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 23 3 degreeUnionState35_115 [3,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_116 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 22 4 degreeUnionState35_116 [4,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_117 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 21 5 degreeUnionState35_117 [5,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_118 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 20 6 degreeUnionState35_118 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_119 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 19 7 degreeUnionState35_119 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_120 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 18 8 degreeUnionState35_120 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_121 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 17 9 degreeUnionState35_121 [9,9] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_114_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 26 9 degreeUnionState35_114 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_115
  · exact degreeUnionBranch35_116
  · exact degreeUnionBranch35_117
  · exact degreeUnionBranch35_118
  · exact degreeUnionBranch35_119
  · exact degreeUnionBranch35_120
  · exact degreeUnionBranch35_121

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_114_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_114_oai
