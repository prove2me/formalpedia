-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_252
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:38:56.337322+00:00
-- url     : https://prove2.me/submissions/ff960bef-5259-4fde-8657-b1a10b6c3cc8

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_253
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_259
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_260
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_261
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_262
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_263
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_264

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_254 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 5 degreeUnionState43_254 [5,15] = true := by
  decide +kernel

lemma degreeUnionBranch43_255 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 6 degreeUnionState43_255 [6,15] = true := by
  decide +kernel

lemma degreeUnionBranch43_256 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 7 degreeUnionState43_256 [7,15] = true := by
  decide +kernel

lemma degreeUnionBranch43_257 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 8 degreeUnionState43_257 [8,15] = true := by
  decide +kernel

lemma degreeUnionBranch43_258 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 9 degreeUnionState43_258 [9,15] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_252_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 28 15 degreeUnionState43_252 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 28 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_253
  · exact degreeUnionBranch43_254
  · exact degreeUnionBranch43_255
  · exact degreeUnionBranch43_256
  · exact degreeUnionBranch43_257
  · exact degreeUnionBranch43_258
  · exact degreeUnionBranch43_259
  · exact degreeUnionBranch43_260
  · exact degreeUnionBranch43_261
  · exact degreeUnionBranch43_262
  · exact degreeUnionBranch43_263
  · exact degreeUnionBranch43_264

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_252_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_252_oai
