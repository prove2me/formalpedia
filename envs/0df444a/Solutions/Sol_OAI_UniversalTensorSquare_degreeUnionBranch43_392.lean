-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_392
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:55:03.333078+00:00
-- url     : https://prove2.me/submissions/cecaf4dd-2886-4f9a-a2ca-2db971395d6f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_393
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_394
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_395
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_396
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_397
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_398
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_399
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_400

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

lemma degreeUnionBranch43_392_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 32 11 degreeUnionState43_392 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_393
  · exact degreeUnionBranch43_394
  · exact degreeUnionBranch43_395
  · exact degreeUnionBranch43_396
  · exact degreeUnionBranch43_397
  · exact degreeUnionBranch43_398
  · exact degreeUnionBranch43_399
  · exact degreeUnionBranch43_400

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_392_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_392_oai
