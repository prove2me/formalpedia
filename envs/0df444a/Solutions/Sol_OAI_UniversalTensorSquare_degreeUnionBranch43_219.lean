-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_219
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:26.912398+00:00
-- url     : https://prove2.me/submissions/faa28b3c-2278-444b-82cc-3f2fd9bbb082

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_220
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_221
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_222
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_223
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_224
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_225
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_226
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_227
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_228

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

lemma degreeUnionBranch43_219_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 31 12 degreeUnionState43_219 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_220
  · exact degreeUnionBranch43_221
  · exact degreeUnionBranch43_222
  · exact degreeUnionBranch43_223
  · exact degreeUnionBranch43_224
  · exact degreeUnionBranch43_225
  · exact degreeUnionBranch43_226
  · exact degreeUnionBranch43_227
  · exact degreeUnionBranch43_228

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_219_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_219_oai
