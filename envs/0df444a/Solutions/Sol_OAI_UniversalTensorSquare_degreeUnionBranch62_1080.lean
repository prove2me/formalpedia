-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1080
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:32:20.117202+00:00
-- url     : https://prove2.me/submissions/95c19fe0-6b03-48f7-b708-75cdc8029488

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1081
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1082
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1083
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1084
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1085

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

lemma degreeUnionBranch62_1086 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 8 degreeUnionState62_1086 [8,9,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_1087 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 21 9 degreeUnionState62_1087 [9,9,11,12] = true := by
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

lemma degreeUnionBranch62_1080_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 9 degreeUnionState62_1080 [9,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1081
  · exact degreeUnionBranch62_1082
  · exact degreeUnionBranch62_1083
  · exact degreeUnionBranch62_1084
  · exact degreeUnionBranch62_1085
  · exact degreeUnionBranch62_1086
  · exact degreeUnionBranch62_1087

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1080_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1080_oai
