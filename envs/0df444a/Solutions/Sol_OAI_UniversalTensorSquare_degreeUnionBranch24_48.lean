-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch24_48
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:26:56.986479+00:00
-- url     : https://prove2.me/submissions/74e2b904-1e65-42ef-b495-0db2f35dd7b2

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

lemma degreeUnionBranch24_49 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 21 3 degreeUnionState24_49 [3] = true := by
  decide +kernel

lemma degreeUnionBranch24_50 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 20 4 degreeUnionState24_50 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_51 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 19 5 degreeUnionState24_51 [5] = true := by
  decide +kernel

lemma degreeUnionBranch24_52 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 18 6 degreeUnionState24_52 [6] = true := by
  decide +kernel

lemma degreeUnionBranch24_53 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 17 7 degreeUnionState24_53 [7] = true := by
  decide +kernel

lemma degreeUnionBranch24_54 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 16 8 degreeUnionState24_54 [8] = true := by
  decide +kernel

lemma degreeUnionBranch24_55 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 15 9 degreeUnionState24_55 [9] = true := by
  decide +kernel

lemma degreeUnionBranch24_56 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 14 10 degreeUnionState24_56 [10] = true := by
  decide +kernel

lemma degreeUnionBranch24_57 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 13 11 degreeUnionState24_57 [11] = true := by
  decide +kernel

lemma degreeUnionBranch24_58 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 12 12 degreeUnionState24_58 [12] = true := by
  decide +kernel

lemma degreeUnionBranch24_59 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 11 13 degreeUnionState24_59 [13] = true := by
  decide +kernel

lemma degreeUnionBranch24_60 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 10 14 degreeUnionState24_60 [14] = true := by
  decide +kernel

lemma degreeUnionBranch24_61 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 9 15 degreeUnionState24_61 [15] = true := by
  decide +kernel

lemma degreeUnionBranch24_62 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 8 16 degreeUnionState24_62 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_63 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 7 17 degreeUnionState24_63 [17] = true := by
  decide +kernel

lemma degreeUnionBranch24_64 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 6 18 degreeUnionState24_64 [18] = true := by
  decide +kernel

lemma degreeUnionBranch24_65 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 5 19 degreeUnionState24_65 [19] = true := by
  decide +kernel

lemma degreeUnionBranch24_66 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 4 20 degreeUnionState24_66 [20] = true := by
  decide +kernel

lemma degreeUnionBranch24_67 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 3 21 degreeUnionState24_67 [21] = true := by
  decide +kernel

lemma degreeUnionBranch24_68 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 2 22 degreeUnionState24_68 [22] = true := by
  decide +kernel

lemma degreeUnionBranch24_69 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 1 23 degreeUnionState24_69 [23] = true := by
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

lemma degreeUnionBranch24_48_oai : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 8 24 23 degreeHalfRegions24 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 23 at hb
  change 24 ≤ 8*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch24_49
  · exact degreeUnionBranch24_50
  · exact degreeUnionBranch24_51
  · exact degreeUnionBranch24_52
  · exact degreeUnionBranch24_53
  · exact degreeUnionBranch24_54
  · exact degreeUnionBranch24_55
  · exact degreeUnionBranch24_56
  · exact degreeUnionBranch24_57
  · exact degreeUnionBranch24_58
  · exact degreeUnionBranch24_59
  · exact degreeUnionBranch24_60
  · exact degreeUnionBranch24_61
  · exact degreeUnionBranch24_62
  · exact degreeUnionBranch24_63
  · exact degreeUnionBranch24_64
  · exact degreeUnionBranch24_65
  · exact degreeUnionBranch24_66
  · exact degreeUnionBranch24_67
  · exact degreeUnionBranch24_68
  · exact degreeUnionBranch24_69

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch24_48_oai := @OAI.UniversalTensorSquare.degreeUnionBranch24_48_oai
