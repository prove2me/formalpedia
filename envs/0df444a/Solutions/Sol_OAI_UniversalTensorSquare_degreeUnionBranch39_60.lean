-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_60
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:10:09.713574+00:00
-- url     : https://prove2.me/submissions/8cfb1dfa-b866-4830-91a9-3fb1047a80de

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

lemma degreeUnionBranch39_61 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 21 4 degreeUnionState39_61 [4,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_62 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 20 5 degreeUnionState39_62 [5,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_63 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 6 degreeUnionState39_63 [6,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_64 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 18 7 degreeUnionState39_64 [7,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_65 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 17 8 degreeUnionState39_65 [8,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_66 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 16 9 degreeUnionState39_66 [9,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_67 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 15 10 degreeUnionState39_67 [10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_68 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 14 11 degreeUnionState39_68 [11,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_69 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 13 12 degreeUnionState39_69 [12,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_70 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 12 13 degreeUnionState39_70 [13,14] = true := by
  decide +kernel

lemma degreeUnionBranch39_71 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 11 14 degreeUnionState39_71 [14,14] = true := by
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

lemma degreeUnionBranch39_60_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 25 14 degreeUnionState39_60 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_61
  · exact degreeUnionBranch39_62
  · exact degreeUnionBranch39_63
  · exact degreeUnionBranch39_64
  · exact degreeUnionBranch39_65
  · exact degreeUnionBranch39_66
  · exact degreeUnionBranch39_67
  · exact degreeUnionBranch39_68
  · exact degreeUnionBranch39_69
  · exact degreeUnionBranch39_70
  · exact degreeUnionBranch39_71

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_60_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_60_oai
