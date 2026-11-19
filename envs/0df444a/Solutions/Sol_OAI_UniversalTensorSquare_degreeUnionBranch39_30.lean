-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:05:05.800024+00:00
-- url     : https://prove2.me/submissions/4bf2a2c1-8f90-4c3e-829c-880a4b438c1c

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

lemma degreeUnionBranch39_31 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 24 4 degreeUnionState39_31 [4,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_32 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 23 5 degreeUnionState39_32 [5,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_33 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 22 6 degreeUnionState39_33 [6,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_34 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 21 7 degreeUnionState39_34 [7,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_35 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 20 8 degreeUnionState39_35 [8,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_36 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 9 degreeUnionState39_36 [9,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_37 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 18 10 degreeUnionState39_37 [10,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_38 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 17 11 degreeUnionState39_38 [11,11] = true := by
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

lemma degreeUnionBranch39_30_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 28 11 degreeUnionState39_30 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 28 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_31
  · exact degreeUnionBranch39_32
  · exact degreeUnionBranch39_33
  · exact degreeUnionBranch39_34
  · exact degreeUnionBranch39_35
  · exact degreeUnionBranch39_36
  · exact degreeUnionBranch39_37
  · exact degreeUnionBranch39_38

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_30_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_30_oai
