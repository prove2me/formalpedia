-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_62
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:02:33.89417+00:00
-- url     : https://prove2.me/submissions/70e112da-764b-4dcd-ae16-f3eec59f49d0

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_131
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_259
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_394
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_67
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_87

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

lemma degreeUnionBranch62_63 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 56 6 degreeUnionState62_63 [6] = true := by
  decide +kernel

lemma degreeUnionBranch62_64 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 55 7 degreeUnionState62_64 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_65 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 54 8 degreeUnionState62_65 [8] = true := by
  decide +kernel

lemma degreeUnionBranch62_66 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 53 9 degreeUnionState62_66 [9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_499 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 47 15 degreeUnionState62_499 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_500 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 46 16 degreeUnionState62_500 [16] = true := by
  decide +kernel

lemma degreeUnionBranch62_501 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 45 17 degreeUnionState62_501 [17] = true := by
  decide +kernel

lemma degreeUnionBranch62_502 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 44 18 degreeUnionState62_502 [18] = true := by
  decide +kernel

lemma degreeUnionBranch62_503 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 43 19 degreeUnionState62_503 [19] = true := by
  decide +kernel

lemma degreeUnionBranch62_504 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 20 degreeUnionState62_504 [20] = true := by
  decide +kernel

lemma degreeUnionBranch62_505 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 21 degreeUnionState62_505 [21] = true := by
  decide +kernel

lemma degreeUnionBranch62_506 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 22 degreeUnionState62_506 [22] = true := by
  decide +kernel

lemma degreeUnionBranch62_507 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 39 23 degreeUnionState62_507 [23] = true := by
  decide +kernel

lemma degreeUnionBranch62_508 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 38 24 degreeUnionState62_508 [24] = true := by
  decide +kernel

lemma degreeUnionBranch62_509 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 37 25 degreeUnionState62_509 [25] = true := by
  decide +kernel

lemma degreeUnionBranch62_510 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 26 degreeUnionState62_510 [26] = true := by
  decide +kernel

lemma degreeUnionBranch62_511 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 35 27 degreeUnionState62_511 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_512 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 28 degreeUnionState62_512 [28] = true := by
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

lemma degreeUnionBranch62_62_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 12*a at hn
  have hlo : 6 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_63
  · exact degreeUnionBranch62_64
  · exact degreeUnionBranch62_65
  · exact degreeUnionBranch62_66
  · exact degreeUnionBranch62_67
  · exact degreeUnionBranch62_87
  · exact degreeUnionBranch62_131
  · exact degreeUnionBranch62_259
  · exact degreeUnionBranch62_394
  · exact degreeUnionBranch62_499
  · exact degreeUnionBranch62_500
  · exact degreeUnionBranch62_501
  · exact degreeUnionBranch62_502
  · exact degreeUnionBranch62_503
  · exact degreeUnionBranch62_504
  · exact degreeUnionBranch62_505
  · exact degreeUnionBranch62_506
  · exact degreeUnionBranch62_507
  · exact degreeUnionBranch62_508
  · exact degreeUnionBranch62_509
  · exact degreeUnionBranch62_510
  · exact degreeUnionBranch62_511
  · exact degreeUnionBranch62_512

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_62_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_62_oai
