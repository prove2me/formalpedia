-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_131
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:04.92217+00:00
-- url     : https://prove2.me/submissions/cdeeef3b-c672-4638-80e1-668ee4800ea3

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

lemma degreeUnionBranch39_132 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 26 4 degreeUnionState39_132 [4,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_133 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 25 5 degreeUnionState39_133 [5,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_134 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 24 6 degreeUnionState39_134 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_135 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 7 degreeUnionState39_135 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_136 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 22 8 degreeUnionState39_136 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_137 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 21 9 degreeUnionState39_137 [9,9] = true := by
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

lemma degreeUnionBranch39_131_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 30 9 degreeUnionState39_131 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_132
  · exact degreeUnionBranch39_133
  · exact degreeUnionBranch39_134
  · exact degreeUnionBranch39_135
  · exact degreeUnionBranch39_136
  · exact degreeUnionBranch39_137

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_131_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_131_oai
