-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:00:06.363246+00:00
-- url     : https://prove2.me/submissions/7e870de0-25e4-4213-b2a7-e8e8b8b9b812

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

lemma degreeUnionBranch39_24 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 24 5 degreeUnionState39_24 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_25 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 23 6 degreeUnionState39_25 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_26 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 22 7 degreeUnionState39_26 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_27 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 21 8 degreeUnionState39_27 [8,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_28 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 20 9 degreeUnionState39_28 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch39_29 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 10 degreeUnionState39_29 [10,10] = true := by
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

lemma degreeUnionBranch39_23_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 29 10 degreeUnionState39_23 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_24
  · exact degreeUnionBranch39_25
  · exact degreeUnionBranch39_26
  · exact degreeUnionBranch39_27
  · exact degreeUnionBranch39_28
  · exact degreeUnionBranch39_29

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_23_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_23_oai
