-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch26_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:27:32.051662+00:00
-- url     : https://prove2.me/submissions/f59d048a-ae43-40a3-827e-091d650ee45c

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 26. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_8 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 22 4 degreeUnionState26_8 [4] = true := by
  decide +kernel

lemma degreeUnionBranch26_9 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 21 5 degreeUnionState26_9 [5] = true := by
  decide +kernel

lemma degreeUnionBranch26_10 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 20 6 degreeUnionState26_10 [6] = true := by
  decide +kernel

lemma degreeUnionBranch26_11 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 19 7 degreeUnionState26_11 [7] = true := by
  decide +kernel

lemma degreeUnionBranch26_12 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 18 8 degreeUnionState26_12 [8] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_13 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 17 9 degreeUnionState26_13 [9] = true := by
  decide +kernel

lemma degreeUnionBranch26_14 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 16 10 degreeUnionState26_14 [10] = true := by
  decide +kernel

lemma degreeUnionBranch26_15 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 15 11 degreeUnionState26_15 [11] = true := by
  decide +kernel

lemma degreeUnionBranch26_16 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 14 12 degreeUnionState26_16 [12] = true := by
  decide +kernel

lemma degreeUnionBranch26_17 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 13 13 degreeUnionState26_17 [13] = true := by
  decide +kernel

lemma degreeUnionBranch26_18 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 12 14 degreeUnionState26_18 [14] = true := by
  decide +kernel

lemma degreeUnionBranch26_19 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 11 15 degreeUnionState26_19 [15] = true := by
  decide +kernel

lemma degreeUnionBranch26_20 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 10 16 degreeUnionState26_20 [16] = true := by
  decide +kernel

lemma degreeUnionBranch26_21 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 9 17 degreeUnionState26_21 [17] = true := by
  decide +kernel

lemma degreeUnionBranch26_22 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 8 18 degreeUnionState26_22 [18] = true := by
  decide +kernel

lemma degreeUnionBranch26_23 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 7 19 degreeUnionState26_23 [19] = true := by
  decide +kernel

lemma degreeUnionBranch26_24 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 6 20 degreeUnionState26_24 [20] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_25 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 5 21 degreeUnionState26_25 [21] = true := by
  decide +kernel

lemma degreeUnionBranch26_26 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 4 22 degreeUnionState26_26 [22] = true := by
  decide +kernel

lemma degreeUnionBranch26_27 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 3 23 degreeUnionState26_27 [23] = true := by
  decide +kernel

lemma degreeUnionBranch26_28 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 2 24 degreeUnionState26_28 [24] = true := by
  decide +kernel

lemma degreeUnionBranch26_29 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 6 1 25 degreeUnionState26_29 [25] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 26. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_7_oai : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 26 25 degreeHalfRegions26 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 25 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch26_8
  · exact degreeUnionBranch26_9
  · exact degreeUnionBranch26_10
  · exact degreeUnionBranch26_11
  · exact degreeUnionBranch26_12
  · exact degreeUnionBranch26_13
  · exact degreeUnionBranch26_14
  · exact degreeUnionBranch26_15
  · exact degreeUnionBranch26_16
  · exact degreeUnionBranch26_17
  · exact degreeUnionBranch26_18
  · exact degreeUnionBranch26_19
  · exact degreeUnionBranch26_20
  · exact degreeUnionBranch26_21
  · exact degreeUnionBranch26_22
  · exact degreeUnionBranch26_23
  · exact degreeUnionBranch26_24
  · exact degreeUnionBranch26_25
  · exact degreeUnionBranch26_26
  · exact degreeUnionBranch26_27
  · exact degreeUnionBranch26_28
  · exact degreeUnionBranch26_29

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch26_7_oai := @OAI.UniversalTensorSquare.degreeUnionBranch26_7_oai
