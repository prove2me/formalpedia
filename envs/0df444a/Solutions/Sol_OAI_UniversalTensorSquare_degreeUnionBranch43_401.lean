-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_401
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:44.366586+00:00
-- url     : https://prove2.me/submissions/03ac5553-1a49-4795-8e0a-5b7f66c239e4

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_402
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_403
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_404
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_405
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_406
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_407
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_408
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_409
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_410

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

lemma degreeUnionBranch43_401_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 31 12 degreeUnionState43_401 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_402
  · exact degreeUnionBranch43_403
  · exact degreeUnionBranch43_404
  · exact degreeUnionBranch43_405
  · exact degreeUnionBranch43_406
  · exact degreeUnionBranch43_407
  · exact degreeUnionBranch43_408
  · exact degreeUnionBranch43_409
  · exact degreeUnionBranch43_410

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_401_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_401_oai
