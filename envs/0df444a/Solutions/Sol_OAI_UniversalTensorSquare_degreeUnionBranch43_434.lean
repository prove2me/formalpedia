-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_434
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:07:59.207327+00:00
-- url     : https://prove2.me/submissions/419cbafd-c2d5-41f4-a79f-3f35f0c4e37e

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_435
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_436
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_437
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_438
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_439
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_440
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_441
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_442
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_443
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_444
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_445
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_446

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

lemma degreeUnionBranch43_434_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 28 15 degreeUnionState43_434 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 28 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_435
  · exact degreeUnionBranch43_436
  · exact degreeUnionBranch43_437
  · exact degreeUnionBranch43_438
  · exact degreeUnionBranch43_439
  · exact degreeUnionBranch43_440
  · exact degreeUnionBranch43_441
  · exact degreeUnionBranch43_442
  · exact degreeUnionBranch43_443
  · exact degreeUnionBranch43_444
  · exact degreeUnionBranch43_445
  · exact degreeUnionBranch43_446

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_434_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_434_oai
