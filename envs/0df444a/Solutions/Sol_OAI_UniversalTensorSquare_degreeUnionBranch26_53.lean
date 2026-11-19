-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch26_53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:27:26.174196+00:00
-- url     : https://prove2.me/submissions/85ac73bc-b237-4ee7-b314-c18d3b4f308a

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

lemma degreeUnionBranch26_54 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 23 3 degreeUnionState26_54 [3] = true := by
  decide +kernel

lemma degreeUnionBranch26_55 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 22 4 degreeUnionState26_55 [4] = true := by
  decide +kernel

lemma degreeUnionBranch26_56 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 21 5 degreeUnionState26_56 [5] = true := by
  decide +kernel

lemma degreeUnionBranch26_57 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 20 6 degreeUnionState26_57 [6] = true := by
  decide +kernel

lemma degreeUnionBranch26_58 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 19 7 degreeUnionState26_58 [7] = true := by
  decide +kernel

lemma degreeUnionBranch26_59 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 18 8 degreeUnionState26_59 [8] = true := by
  decide +kernel

lemma degreeUnionBranch26_60 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 17 9 degreeUnionState26_60 [9] = true := by
  decide +kernel

lemma degreeUnionBranch26_61 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 16 10 degreeUnionState26_61 [10] = true := by
  decide +kernel

lemma degreeUnionBranch26_62 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 15 11 degreeUnionState26_62 [11] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_63 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 14 12 degreeUnionState26_63 [12] = true := by
  decide +kernel

lemma degreeUnionBranch26_64 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 13 13 degreeUnionState26_64 [13] = true := by
  decide +kernel

lemma degreeUnionBranch26_65 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 12 14 degreeUnionState26_65 [14] = true := by
  decide +kernel

lemma degreeUnionBranch26_66 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 11 15 degreeUnionState26_66 [15] = true := by
  decide +kernel

lemma degreeUnionBranch26_67 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 10 16 degreeUnionState26_67 [16] = true := by
  decide +kernel

lemma degreeUnionBranch26_68 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 9 17 degreeUnionState26_68 [17] = true := by
  decide +kernel

lemma degreeUnionBranch26_69 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 8 18 degreeUnionState26_69 [18] = true := by
  decide +kernel

lemma degreeUnionBranch26_70 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 7 19 degreeUnionState26_70 [19] = true := by
  decide +kernel

lemma degreeUnionBranch26_71 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 6 20 degreeUnionState26_71 [20] = true := by
  decide +kernel

lemma degreeUnionBranch26_72 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 5 21 degreeUnionState26_72 [21] = true := by
  decide +kernel

lemma degreeUnionBranch26_73 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 4 22 degreeUnionState26_73 [22] = true := by
  decide +kernel

lemma degreeUnionBranch26_74 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 3 23 degreeUnionState26_74 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_75 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 2 24 degreeUnionState26_75 [24] = true := by
  decide +kernel

lemma degreeUnionBranch26_76 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 1 25 degreeUnionState26_76 [25] = true := by
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

lemma degreeUnionBranch26_53_oai : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 9 26 25 degreeHalfRegions26 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 25 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch26_54
  · exact degreeUnionBranch26_55
  · exact degreeUnionBranch26_56
  · exact degreeUnionBranch26_57
  · exact degreeUnionBranch26_58
  · exact degreeUnionBranch26_59
  · exact degreeUnionBranch26_60
  · exact degreeUnionBranch26_61
  · exact degreeUnionBranch26_62
  · exact degreeUnionBranch26_63
  · exact degreeUnionBranch26_64
  · exact degreeUnionBranch26_65
  · exact degreeUnionBranch26_66
  · exact degreeUnionBranch26_67
  · exact degreeUnionBranch26_68
  · exact degreeUnionBranch26_69
  · exact degreeUnionBranch26_70
  · exact degreeUnionBranch26_71
  · exact degreeUnionBranch26_72
  · exact degreeUnionBranch26_73
  · exact degreeUnionBranch26_74
  · exact degreeUnionBranch26_75
  · exact degreeUnionBranch26_76

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch26_53_oai := @OAI.UniversalTensorSquare.degreeUnionBranch26_53_oai
