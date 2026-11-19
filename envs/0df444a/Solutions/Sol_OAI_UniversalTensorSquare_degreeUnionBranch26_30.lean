-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch26_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:27:20.504827+00:00
-- url     : https://prove2.me/submissions/07fafeec-05a7-4a0f-a748-adaafbecf36b

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

lemma degreeUnionBranch26_31 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 22 4 degreeUnionState26_31 [4] = true := by
  decide +kernel

lemma degreeUnionBranch26_32 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 21 5 degreeUnionState26_32 [5] = true := by
  decide +kernel

lemma degreeUnionBranch26_33 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 20 6 degreeUnionState26_33 [6] = true := by
  decide +kernel

lemma degreeUnionBranch26_34 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 19 7 degreeUnionState26_34 [7] = true := by
  decide +kernel

lemma degreeUnionBranch26_35 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 18 8 degreeUnionState26_35 [8] = true := by
  decide +kernel

lemma degreeUnionBranch26_36 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 17 9 degreeUnionState26_36 [9] = true := by
  decide +kernel

lemma degreeUnionBranch26_37 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 16 10 degreeUnionState26_37 [10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_38 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 15 11 degreeUnionState26_38 [11] = true := by
  decide +kernel

lemma degreeUnionBranch26_39 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 14 12 degreeUnionState26_39 [12] = true := by
  decide +kernel

lemma degreeUnionBranch26_40 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 13 13 degreeUnionState26_40 [13] = true := by
  decide +kernel

lemma degreeUnionBranch26_41 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 12 14 degreeUnionState26_41 [14] = true := by
  decide +kernel

lemma degreeUnionBranch26_42 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 11 15 degreeUnionState26_42 [15] = true := by
  decide +kernel

lemma degreeUnionBranch26_43 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 10 16 degreeUnionState26_43 [16] = true := by
  decide +kernel

lemma degreeUnionBranch26_44 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 9 17 degreeUnionState26_44 [17] = true := by
  decide +kernel

lemma degreeUnionBranch26_45 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 8 18 degreeUnionState26_45 [18] = true := by
  decide +kernel

lemma degreeUnionBranch26_46 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 7 19 degreeUnionState26_46 [19] = true := by
  decide +kernel

lemma degreeUnionBranch26_47 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 6 20 degreeUnionState26_47 [20] = true := by
  decide +kernel

lemma degreeUnionBranch26_48 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 5 21 degreeUnionState26_48 [21] = true := by
  decide +kernel

lemma degreeUnionBranch26_49 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 4 22 degreeUnionState26_49 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_50 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 3 23 degreeUnionState26_50 [23] = true := by
  decide +kernel

lemma degreeUnionBranch26_51 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 2 24 degreeUnionState26_51 [24] = true := by
  decide +kernel

lemma degreeUnionBranch26_52 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 1 25 degreeUnionState26_52 [25] = true := by
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

lemma degreeUnionBranch26_30_oai : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 26 25 degreeHalfRegions26 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 25 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch26_31
  · exact degreeUnionBranch26_32
  · exact degreeUnionBranch26_33
  · exact degreeUnionBranch26_34
  · exact degreeUnionBranch26_35
  · exact degreeUnionBranch26_36
  · exact degreeUnionBranch26_37
  · exact degreeUnionBranch26_38
  · exact degreeUnionBranch26_39
  · exact degreeUnionBranch26_40
  · exact degreeUnionBranch26_41
  · exact degreeUnionBranch26_42
  · exact degreeUnionBranch26_43
  · exact degreeUnionBranch26_44
  · exact degreeUnionBranch26_45
  · exact degreeUnionBranch26_46
  · exact degreeUnionBranch26_47
  · exact degreeUnionBranch26_48
  · exact degreeUnionBranch26_49
  · exact degreeUnionBranch26_50
  · exact degreeUnionBranch26_51
  · exact degreeUnionBranch26_52

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch26_30_oai := @OAI.UniversalTensorSquare.degreeUnionBranch26_30_oai
