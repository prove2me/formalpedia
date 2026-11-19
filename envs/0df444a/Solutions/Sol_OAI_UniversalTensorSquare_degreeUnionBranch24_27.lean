-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch24_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:26:51.351508+00:00
-- url     : https://prove2.me/submissions/916c6703-a9be-4807-a867-4f1ad2ac5ab2

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

lemma degreeUnionBranch24_28 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 20 4 degreeUnionState24_28 [4] = true := by
  decide +kernel

lemma degreeUnionBranch24_29 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 19 5 degreeUnionState24_29 [5] = true := by
  decide +kernel

lemma degreeUnionBranch24_30 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 18 6 degreeUnionState24_30 [6] = true := by
  decide +kernel

lemma degreeUnionBranch24_31 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 17 7 degreeUnionState24_31 [7] = true := by
  decide +kernel

lemma degreeUnionBranch24_32 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 16 8 degreeUnionState24_32 [8] = true := by
  decide +kernel

lemma degreeUnionBranch24_33 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 15 9 degreeUnionState24_33 [9] = true := by
  decide +kernel

lemma degreeUnionBranch24_34 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 14 10 degreeUnionState24_34 [10] = true := by
  decide +kernel

lemma degreeUnionBranch24_35 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 13 11 degreeUnionState24_35 [11] = true := by
  decide +kernel

lemma degreeUnionBranch24_36 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 12 12 degreeUnionState24_36 [12] = true := by
  decide +kernel

lemma degreeUnionBranch24_37 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 11 13 degreeUnionState24_37 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_38 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 10 14 degreeUnionState24_38 [14] = true := by
  decide +kernel

lemma degreeUnionBranch24_39 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 9 15 degreeUnionState24_39 [15] = true := by
  decide +kernel

lemma degreeUnionBranch24_40 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 8 16 degreeUnionState24_40 [16] = true := by
  decide +kernel

lemma degreeUnionBranch24_41 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 7 17 degreeUnionState24_41 [17] = true := by
  decide +kernel

lemma degreeUnionBranch24_42 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 6 18 degreeUnionState24_42 [18] = true := by
  decide +kernel

lemma degreeUnionBranch24_43 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 5 19 degreeUnionState24_43 [19] = true := by
  decide +kernel

lemma degreeUnionBranch24_44 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 4 20 degreeUnionState24_44 [20] = true := by
  decide +kernel

lemma degreeUnionBranch24_45 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 3 21 degreeUnionState24_45 [21] = true := by
  decide +kernel

lemma degreeUnionBranch24_46 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 2 22 degreeUnionState24_46 [22] = true := by
  decide +kernel

lemma degreeUnionBranch24_47 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 1 23 degreeUnionState24_47 [23] = true := by
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

lemma degreeUnionBranch24_27_oai : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 24 23 degreeHalfRegions24 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 23 at hb
  change 24 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch24_28
  · exact degreeUnionBranch24_29
  · exact degreeUnionBranch24_30
  · exact degreeUnionBranch24_31
  · exact degreeUnionBranch24_32
  · exact degreeUnionBranch24_33
  · exact degreeUnionBranch24_34
  · exact degreeUnionBranch24_35
  · exact degreeUnionBranch24_36
  · exact degreeUnionBranch24_37
  · exact degreeUnionBranch24_38
  · exact degreeUnionBranch24_39
  · exact degreeUnionBranch24_40
  · exact degreeUnionBranch24_41
  · exact degreeUnionBranch24_42
  · exact degreeUnionBranch24_43
  · exact degreeUnionBranch24_44
  · exact degreeUnionBranch24_45
  · exact degreeUnionBranch24_46
  · exact degreeUnionBranch24_47

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch24_27_oai := @OAI.UniversalTensorSquare.degreeUnionBranch24_27_oai
