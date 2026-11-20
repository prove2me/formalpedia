-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_442
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:15.745318+00:00
-- url     : https://prove2.me/submissions/a88c6861-6b64-489e-8ddd-f2c1d2ac22b4

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_443
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_444
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_445
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_446
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_451
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_457
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_464

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

lemma degreeUnionBranch62_442_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 10 degreeUnionState62_442 [10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 38 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_443
  · exact degreeUnionBranch62_444
  · exact degreeUnionBranch62_445
  · exact degreeUnionBranch62_446
  · exact degreeUnionBranch62_451
  · exact degreeUnionBranch62_457
  · exact degreeUnionBranch62_464

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_442_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_442_oai
