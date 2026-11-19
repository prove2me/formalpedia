-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_85
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:10:27.224184+00:00
-- url     : https://prove2.me/submissions/40f4b87d-7ec3-45e0-87cc-c64e89b66c65

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

lemma degreeUnionBranch39_86 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 4 degreeUnionState39_86 [4,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_87 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 18 5 degreeUnionState39_87 [5,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_88 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 17 6 degreeUnionState39_88 [6,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_89 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 16 7 degreeUnionState39_89 [7,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_90 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 15 8 degreeUnionState39_90 [8,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_91 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 14 9 degreeUnionState39_91 [9,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_92 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 13 10 degreeUnionState39_92 [10,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_93 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 12 11 degreeUnionState39_93 [11,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_94 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 11 12 degreeUnionState39_94 [12,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_95 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 10 13 degreeUnionState39_95 [13,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_96 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 9 14 degreeUnionState39_96 [14,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_97 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 8 15 degreeUnionState39_97 [15,16] = true := by
  decide +kernel

lemma degreeUnionBranch39_98 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 7 16 degreeUnionState39_98 [16,16] = true := by
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

lemma degreeUnionBranch39_85_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 16 degreeUnionState39_85 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 23 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_86
  · exact degreeUnionBranch39_87
  · exact degreeUnionBranch39_88
  · exact degreeUnionBranch39_89
  · exact degreeUnionBranch39_90
  · exact degreeUnionBranch39_91
  · exact degreeUnionBranch39_92
  · exact degreeUnionBranch39_93
  · exact degreeUnionBranch39_94
  · exact degreeUnionBranch39_95
  · exact degreeUnionBranch39_96
  · exact degreeUnionBranch39_97
  · exact degreeUnionBranch39_98

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_85_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_85_oai
