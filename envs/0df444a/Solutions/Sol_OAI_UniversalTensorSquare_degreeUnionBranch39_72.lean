-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_72
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:10:15.538087+00:00
-- url     : https://prove2.me/submissions/578ca30d-a5fb-4dfd-8e44-a8c744e81331

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

lemma degreeUnionBranch39_73 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 20 4 degreeUnionState39_73 [4,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_74 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 5 degreeUnionState39_74 [5,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_75 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 18 6 degreeUnionState39_75 [6,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_76 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 17 7 degreeUnionState39_76 [7,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_77 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 16 8 degreeUnionState39_77 [8,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_78 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 15 9 degreeUnionState39_78 [9,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_79 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 14 10 degreeUnionState39_79 [10,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_80 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 13 11 degreeUnionState39_80 [11,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_81 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 12 12 degreeUnionState39_81 [12,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_82 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 11 13 degreeUnionState39_82 [13,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_83 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 10 14 degreeUnionState39_83 [14,15] = true := by
  decide +kernel

lemma degreeUnionBranch39_84 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 9 15 degreeUnionState39_84 [15,15] = true := by
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

lemma degreeUnionBranch39_72_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 24 15 degreeUnionState39_72 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 24 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_73
  · exact degreeUnionBranch39_74
  · exact degreeUnionBranch39_75
  · exact degreeUnionBranch39_76
  · exact degreeUnionBranch39_77
  · exact degreeUnionBranch39_78
  · exact degreeUnionBranch39_79
  · exact degreeUnionBranch39_80
  · exact degreeUnionBranch39_81
  · exact degreeUnionBranch39_82
  · exact degreeUnionBranch39_83
  · exact degreeUnionBranch39_84

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_72_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_72_oai
