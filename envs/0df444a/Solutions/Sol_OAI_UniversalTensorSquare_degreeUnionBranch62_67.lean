-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_67
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:02:39.871225+00:00
-- url     : https://prove2.me/submissions/126b86d2-6593-4f14-9a7b-9d8b48666b93

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_68 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 47 5 degreeUnionState62_68 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_69 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 46 6 degreeUnionState62_69 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_70 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 45 7 degreeUnionState62_70 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_71 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 44 8 degreeUnionState62_71 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_72 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 43 9 degreeUnionState62_72 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_74 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 37 5 degreeUnionState62_74 [5,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_75 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 36 6 degreeUnionState62_75 [6,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_76 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 7 degreeUnionState62_76 [7,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_77 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 8 degreeUnionState62_77 [8,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_78 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 9 degreeUnionState62_78 [9,10,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_80 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 4 degreeUnionState62_80 [4,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_81 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 5 degreeUnionState62_81 [5,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_82 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 6 degreeUnionState62_82 [6,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_83 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 7 degreeUnionState62_83 [7,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_84 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 8 degreeUnionState62_84 [8,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_85 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 9 degreeUnionState62_85 [9,10,10,10] = true := by
  decide +kernel

lemma degreeUnionBranch62_86 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 10 degreeUnionState62_86 [10,10,10,10] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_79 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 10 degreeUnionState62_79 [10,10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_80
  · exact degreeUnionBranch62_81
  · exact degreeUnionBranch62_82
  · exact degreeUnionBranch62_83
  · exact degreeUnionBranch62_84
  · exact degreeUnionBranch62_85
  · exact degreeUnionBranch62_86

lemma degreeUnionBranch62_73 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 42 10 degreeUnionState62_73 [10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 42 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_74
  · exact degreeUnionBranch62_75
  · exact degreeUnionBranch62_76
  · exact degreeUnionBranch62_77
  · exact degreeUnionBranch62_78
  · exact degreeUnionBranch62_79

lemma degreeUnionBranch62_67_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 52 10 degreeUnionState62_67 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 52 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_68
  · exact degreeUnionBranch62_69
  · exact degreeUnionBranch62_70
  · exact degreeUnionBranch62_71
  · exact degreeUnionBranch62_72
  · exact degreeUnionBranch62_73

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_67_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_67_oai
