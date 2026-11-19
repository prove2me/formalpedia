-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1051
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:18:21.947626+00:00
-- url     : https://prove2.me/submissions/f8262179-dec2-4e28-b26d-788b90579433

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1052
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1053
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1054

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

lemma degreeUnionBranch62_1055 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 6 degreeUnionState62_1055 [6,9,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1056 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 7 degreeUnionState62_1056 [7,9,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1057 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 8 degreeUnionState62_1057 [8,9,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1058 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 9 degreeUnionState62_1058 [9,9,10,12] = true := by
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

lemma degreeUnionBranch62_1051_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 9 degreeUnionState62_1051 [9,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1052
  · exact degreeUnionBranch62_1053
  · exact degreeUnionBranch62_1054
  · exact degreeUnionBranch62_1055
  · exact degreeUnionBranch62_1056
  · exact degreeUnionBranch62_1057
  · exact degreeUnionBranch62_1058

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1051_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1051_oai
