-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_225
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:59:42.080443+00:00
-- url     : https://prove2.me/submissions/b610948b-dd7d-402a-84ef-adcc87ccf645

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_226
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_227
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_228
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_230
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_236
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_243
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_251
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_260
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_271
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_283
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_284
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_285
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_286
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_287
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_288
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_289
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_290
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_291
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_292
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_293
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_294
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_295
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_296
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_297
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_298
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_299
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_300
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_301
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_302
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_303
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_304
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_305
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_306
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_307

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_229 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 32 7 degreeUnionState39_229 [7] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_225_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 10 39 38 degreeHalfRegions39 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 38 at hb
  change 39 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_226
  · exact degreeUnionBranch39_227
  · exact degreeUnionBranch39_228
  · exact degreeUnionBranch39_229
  · exact degreeUnionBranch39_230
  · exact degreeUnionBranch39_236
  · exact degreeUnionBranch39_243
  · exact degreeUnionBranch39_251
  · exact degreeUnionBranch39_260
  · exact degreeUnionBranch39_271
  · exact degreeUnionBranch39_283
  · exact degreeUnionBranch39_284
  · exact degreeUnionBranch39_285
  · exact degreeUnionBranch39_286
  · exact degreeUnionBranch39_287
  · exact degreeUnionBranch39_288
  · exact degreeUnionBranch39_289
  · exact degreeUnionBranch39_290
  · exact degreeUnionBranch39_291
  · exact degreeUnionBranch39_292
  · exact degreeUnionBranch39_293
  · exact degreeUnionBranch39_294
  · exact degreeUnionBranch39_295
  · exact degreeUnionBranch39_296
  · exact degreeUnionBranch39_297
  · exact degreeUnionBranch39_298
  · exact degreeUnionBranch39_299
  · exact degreeUnionBranch39_300
  · exact degreeUnionBranch39_301
  · exact degreeUnionBranch39_302
  · exact degreeUnionBranch39_303
  · exact degreeUnionBranch39_304
  · exact degreeUnionBranch39_305
  · exact degreeUnionBranch39_306
  · exact degreeUnionBranch39_307

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_225_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_225_oai
