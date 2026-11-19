-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:48.841234+00:00
-- url     : https://prove2.me/submissions/3684d2fd-bb2a-4576-a117-c11c071338c2

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_241
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_242
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_243
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_244
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_245
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_246
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_247
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_248
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_249
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_250
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_251

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_240_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 29 14 degreeUnionState43_240 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 29 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_241
  · exact degreeUnionBranch43_242
  · exact degreeUnionBranch43_243
  · exact degreeUnionBranch43_244
  · exact degreeUnionBranch43_245
  · exact degreeUnionBranch43_246
  · exact degreeUnionBranch43_247
  · exact degreeUnionBranch43_248
  · exact degreeUnionBranch43_249
  · exact degreeUnionBranch43_250
  · exact degreeUnionBranch43_251

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_240_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_240_oai
