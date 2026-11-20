-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_173
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:42:06.101397+00:00
-- url     : https://prove2.me/submissions/36103ecb-507e-4633-965d-04c5a0c9f177

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_174
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_175
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_176
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_177
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_182
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_188
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_195

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

lemma degreeUnionBranch62_173_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 40 10 degreeUnionState62_173 [10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 40 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_174
  · exact degreeUnionBranch62_175
  · exact degreeUnionBranch62_176
  · exact degreeUnionBranch62_177
  · exact degreeUnionBranch62_182
  · exact degreeUnionBranch62_188
  · exact degreeUnionBranch62_195

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_173_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_173_oai
