-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_306
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:58:03.371952+00:00
-- url     : https://prove2.me/submissions/d3bce63a-45d2-4890-8cef-2a65f9b70441

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_307
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_308
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_309
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_310
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_315
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_321
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_328

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

lemma degreeUnionBranch62_306_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 39 10 degreeUnionState62_306 [10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 39 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_307
  · exact degreeUnionBranch62_308
  · exact degreeUnionBranch62_309
  · exact degreeUnionBranch62_310
  · exact degreeUnionBranch62_315
  · exact degreeUnionBranch62_321
  · exact degreeUnionBranch62_328

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_306_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_306_oai
