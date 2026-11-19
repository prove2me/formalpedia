-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_265
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:39:49.677471+00:00
-- url     : https://prove2.me/submissions/c8db46a8-9f4e-4a33-b3ea-a2136caaa43a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_272
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_273
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_274
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_275
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_276
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_277
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_278

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

lemma degreeUnionBranch43_266 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 4 degreeUnionState43_266 [4,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_267 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 5 degreeUnionState43_267 [5,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_268 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 6 degreeUnionState43_268 [6,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_269 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 7 degreeUnionState43_269 [7,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_270 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 8 degreeUnionState43_270 [8,16] = true := by
  decide +kernel

lemma degreeUnionBranch43_271 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 9 degreeUnionState43_271 [9,16] = true := by
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

lemma degreeUnionBranch43_265_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 27 16 degreeUnionState43_265 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_266
  · exact degreeUnionBranch43_267
  · exact degreeUnionBranch43_268
  · exact degreeUnionBranch43_269
  · exact degreeUnionBranch43_270
  · exact degreeUnionBranch43_271
  · exact degreeUnionBranch43_272
  · exact degreeUnionBranch43_273
  · exact degreeUnionBranch43_274
  · exact degreeUnionBranch43_275
  · exact degreeUnionBranch43_276
  · exact degreeUnionBranch43_277
  · exact degreeUnionBranch43_278

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_265_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_265_oai
