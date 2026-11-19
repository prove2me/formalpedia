-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_422
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:04:01.019131+00:00
-- url     : https://prove2.me/submissions/bcaf6de0-b0b0-414b-9d39-16e556cd177a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_423
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_424
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_425
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_426
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_427
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_428
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_429
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_430
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_431
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_432
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_433

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

lemma degreeUnionBranch43_422_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 29 14 degreeUnionState43_422 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_423
  · exact degreeUnionBranch43_424
  · exact degreeUnionBranch43_425
  · exact degreeUnionBranch43_426
  · exact degreeUnionBranch43_427
  · exact degreeUnionBranch43_428
  · exact degreeUnionBranch43_429
  · exact degreeUnionBranch43_430
  · exact degreeUnionBranch43_431
  · exact degreeUnionBranch43_432
  · exact degreeUnionBranch43_433

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_422_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_422_oai
