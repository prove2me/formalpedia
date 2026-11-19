-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:51:33.934497+00:00
-- url     : https://prove2.me/submissions/0dcdeaa3-a2bd-4a43-8ff7-29338a3a2c31

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

lemma degreeUnionBranch39_18 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 25 5 degreeUnionState39_18 [5,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_19 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 24 6 degreeUnionState39_19 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_20 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 23 7 degreeUnionState39_20 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_21 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 22 8 degreeUnionState39_21 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_22 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 21 9 degreeUnionState39_22 [9,9] = true := by
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

lemma degreeUnionBranch39_17_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 30 9 degreeUnionState39_17 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_18
  · exact degreeUnionBranch39_19
  · exact degreeUnionBranch39_20
  · exact degreeUnionBranch39_21
  · exact degreeUnionBranch39_22

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_17_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_17_oai
