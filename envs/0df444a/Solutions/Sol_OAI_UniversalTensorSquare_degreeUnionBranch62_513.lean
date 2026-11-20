-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_513
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:02:21.782748+00:00
-- url     : https://prove2.me/submissions/15247435-6ebd-47d9-8891-35f1afd29c89

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_519
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_540
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_587
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_707
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_834

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

lemma degreeUnionBranch62_514 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 57 5 degreeUnionState62_514 [5] = true := by
  decide +kernel

lemma degreeUnionBranch62_515 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 56 6 degreeUnionState62_515 [6] = true := by
  decide +kernel

lemma degreeUnionBranch62_516 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 55 7 degreeUnionState62_516 [7] = true := by
  decide +kernel

lemma degreeUnionBranch62_517 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 54 8 degreeUnionState62_517 [8] = true := by
  decide +kernel

lemma degreeUnionBranch62_518 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 53 9 degreeUnionState62_518 [9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_934 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 47 15 degreeUnionState62_934 [15] = true := by
  decide +kernel

lemma degreeUnionBranch62_935 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 46 16 degreeUnionState62_935 [16] = true := by
  decide +kernel

lemma degreeUnionBranch62_936 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 45 17 degreeUnionState62_936 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_937 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 44 18 degreeUnionState62_937 [18] = true := by
  decide +kernel

lemma degreeUnionBranch62_938 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 43 19 degreeUnionState62_938 [19] = true := by
  decide +kernel

lemma degreeUnionBranch62_939 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 42 20 degreeUnionState62_939 [20] = true := by
  decide +kernel

lemma degreeUnionBranch62_940 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 41 21 degreeUnionState62_940 [21] = true := by
  decide +kernel

lemma degreeUnionBranch62_941 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 22 degreeUnionState62_941 [22] = true := by
  decide +kernel

lemma degreeUnionBranch62_942 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 39 23 degreeUnionState62_942 [23] = true := by
  decide +kernel

lemma degreeUnionBranch62_943 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 38 24 degreeUnionState62_943 [24] = true := by
  decide +kernel

lemma degreeUnionBranch62_944 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 37 25 degreeUnionState62_944 [25] = true := by
  decide +kernel

lemma degreeUnionBranch62_945 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 36 26 degreeUnionState62_945 [26] = true := by
  decide +kernel

lemma degreeUnionBranch62_946 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 35 27 degreeUnionState62_946 [27] = true := by
  decide +kernel

lemma degreeUnionBranch62_947 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 34 28 degreeUnionState62_947 [28] = true := by
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

lemma degreeUnionBranch62_513_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 13*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_514
  · exact degreeUnionBranch62_515
  · exact degreeUnionBranch62_516
  · exact degreeUnionBranch62_517
  · exact degreeUnionBranch62_518
  · exact degreeUnionBranch62_519
  · exact degreeUnionBranch62_540
  · exact degreeUnionBranch62_587
  · exact degreeUnionBranch62_707
  · exact degreeUnionBranch62_834
  · exact degreeUnionBranch62_934
  · exact degreeUnionBranch62_935
  · exact degreeUnionBranch62_936
  · exact degreeUnionBranch62_937
  · exact degreeUnionBranch62_938
  · exact degreeUnionBranch62_939
  · exact degreeUnionBranch62_940
  · exact degreeUnionBranch62_941
  · exact degreeUnionBranch62_942
  · exact degreeUnionBranch62_943
  · exact degreeUnionBranch62_944
  · exact degreeUnionBranch62_945
  · exact degreeUnionBranch62_946
  · exact degreeUnionBranch62_947

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_513_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_513_oai
