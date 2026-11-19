-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch24_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:27:02.776346+00:00
-- url     : https://prove2.me/submissions/3a895ef4-d842-43b1-a794-ba34078cdac4

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 24. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_7 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 20 4 degreeUnionState24_7 [4] = true := by
  decide +kernel

lemma degreeUnionBranch24_8 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 19 5 degreeUnionState24_8 [5] = true := by
  decide +kernel

lemma degreeUnionBranch24_9 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 18 6 degreeUnionState24_9 [6] = true := by
  decide +kernel

lemma degreeUnionBranch24_10 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 17 7 degreeUnionState24_10 [7] = true := by
  decide +kernel

lemma degreeUnionBranch24_11 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 16 8 degreeUnionState24_11 [8] = true := by
  decide +kernel

lemma degreeUnionBranch24_12 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 15 9 degreeUnionState24_12 [9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_13 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 14 10 degreeUnionState24_13 [10] = true := by
  decide +kernel

lemma degreeUnionBranch24_14 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 13 11 degreeUnionState24_14 [11] = true := by
  decide +kernel

lemma degreeUnionBranch24_15 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 12 12 degreeUnionState24_15 [12] = true := by
  decide +kernel

lemma degreeUnionBranch24_16 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 11 13 degreeUnionState24_16 [13] = true := by
  decide +kernel

lemma degreeUnionBranch24_17 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 10 14 degreeUnionState24_17 [14] = true := by
  decide +kernel

lemma degreeUnionBranch24_18 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 9 15 degreeUnionState24_18 [15] = true := by
  decide +kernel

lemma degreeUnionBranch24_19 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 8 16 degreeUnionState24_19 [16] = true := by
  decide +kernel

lemma degreeUnionBranch24_20 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 7 17 degreeUnionState24_20 [17] = true := by
  decide +kernel

lemma degreeUnionBranch24_21 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 6 18 degreeUnionState24_21 [18] = true := by
  decide +kernel

lemma degreeUnionBranch24_22 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 5 19 degreeUnionState24_22 [19] = true := by
  decide +kernel

lemma degreeUnionBranch24_23 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 4 20 degreeUnionState24_23 [20] = true := by
  decide +kernel

lemma degreeUnionBranch24_24 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 3 21 degreeUnionState24_24 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_25 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 2 22 degreeUnionState24_25 [22] = true := by
  decide +kernel

lemma degreeUnionBranch24_26 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 5 1 23 degreeUnionState24_26 [23] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 24. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_6_oai : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 24 23 degreeHalfRegions24 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 23 at hb
  change 24 ≤ 6*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch24_7
  · exact degreeUnionBranch24_8
  · exact degreeUnionBranch24_9
  · exact degreeUnionBranch24_10
  · exact degreeUnionBranch24_11
  · exact degreeUnionBranch24_12
  · exact degreeUnionBranch24_13
  · exact degreeUnionBranch24_14
  · exact degreeUnionBranch24_15
  · exact degreeUnionBranch24_16
  · exact degreeUnionBranch24_17
  · exact degreeUnionBranch24_18
  · exact degreeUnionBranch24_19
  · exact degreeUnionBranch24_20
  · exact degreeUnionBranch24_21
  · exact degreeUnionBranch24_22
  · exact degreeUnionBranch24_23
  · exact degreeUnionBranch24_24
  · exact degreeUnionBranch24_25
  · exact degreeUnionBranch24_26

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch24_6_oai := @OAI.UniversalTensorSquare.degreeUnionBranch24_6_oai
