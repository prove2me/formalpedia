-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_49
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:10:03.401948+00:00
-- url     : https://prove2.me/submissions/01287c0b-85cb-43cb-aec7-88471dc1a7a2

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

lemma degreeUnionBranch39_50 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 22 4 degreeUnionState39_50 [4,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_51 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 21 5 degreeUnionState39_51 [5,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_52 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 20 6 degreeUnionState39_52 [6,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_53 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 7 degreeUnionState39_53 [7,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_54 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 18 8 degreeUnionState39_54 [8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_55 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 17 9 degreeUnionState39_55 [9,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_56 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 16 10 degreeUnionState39_56 [10,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_57 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 15 11 degreeUnionState39_57 [11,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_58 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 14 12 degreeUnionState39_58 [12,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_59 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 13 13 degreeUnionState39_59 [13,13] = true := by
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

lemma degreeUnionBranch39_49_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 26 13 degreeUnionState39_49 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_50
  · exact degreeUnionBranch39_51
  · exact degreeUnionBranch39_52
  · exact degreeUnionBranch39_53
  · exact degreeUnionBranch39_54
  · exact degreeUnionBranch39_55
  · exact degreeUnionBranch39_56
  · exact degreeUnionBranch39_57
  · exact degreeUnionBranch39_58
  · exact degreeUnionBranch39_59

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_49_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_49_oai
