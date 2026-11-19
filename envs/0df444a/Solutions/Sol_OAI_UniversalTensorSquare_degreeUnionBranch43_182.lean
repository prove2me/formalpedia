-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_182
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:20:37.177194+00:00
-- url     : https://prove2.me/submissions/042cd1eb-4114-41c2-9bfc-a8df56ab5678

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_183
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_184
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_185
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_186
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_191
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_203
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_210
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_219
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_229
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_240
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_252
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_265
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_279
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_294
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_310
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_328
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_329
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_330
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_331
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_332
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_333
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_334
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_335
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_336
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_337
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_338
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_339
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_340
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_341
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_342
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_343
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_344
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_345
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_346
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_347
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_348
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_349
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_350

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

lemma degreeUnionBranch43_182_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 9*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_183
  · exact degreeUnionBranch43_184
  · exact degreeUnionBranch43_185
  · exact degreeUnionBranch43_186
  · exact degreeUnionBranch43_191
  · exact degreeUnionBranch43_203
  · exact degreeUnionBranch43_210
  · exact degreeUnionBranch43_219
  · exact degreeUnionBranch43_229
  · exact degreeUnionBranch43_240
  · exact degreeUnionBranch43_252
  · exact degreeUnionBranch43_265
  · exact degreeUnionBranch43_279
  · exact degreeUnionBranch43_294
  · exact degreeUnionBranch43_310
  · exact degreeUnionBranch43_328
  · exact degreeUnionBranch43_329
  · exact degreeUnionBranch43_330
  · exact degreeUnionBranch43_331
  · exact degreeUnionBranch43_332
  · exact degreeUnionBranch43_333
  · exact degreeUnionBranch43_334
  · exact degreeUnionBranch43_335
  · exact degreeUnionBranch43_336
  · exact degreeUnionBranch43_337
  · exact degreeUnionBranch43_338
  · exact degreeUnionBranch43_339
  · exact degreeUnionBranch43_340
  · exact degreeUnionBranch43_341
  · exact degreeUnionBranch43_342
  · exact degreeUnionBranch43_343
  · exact degreeUnionBranch43_344
  · exact degreeUnionBranch43_345
  · exact degreeUnionBranch43_346
  · exact degreeUnionBranch43_347
  · exact degreeUnionBranch43_348
  · exact degreeUnionBranch43_349
  · exact degreeUnionBranch43_350

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_182_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_182_oai
