-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:26:14.919703+00:00
-- url     : https://prove2.me/submissions/2db98bf9-9d12-410f-920b-e812b7b8d63b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_28
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_29
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_30
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_31
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_32
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_33
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_34
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_35
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_36

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

lemma degreeUnionBranch62_27_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 49 13 degreeUnionState62_27 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 49 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_28
  · exact degreeUnionBranch62_29
  · exact degreeUnionBranch62_30
  · exact degreeUnionBranch62_31
  · exact degreeUnionBranch62_32
  · exact degreeUnionBranch62_33
  · exact degreeUnionBranch62_34
  · exact degreeUnionBranch62_35
  · exact degreeUnionBranch62_36

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_27_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_27_oai
