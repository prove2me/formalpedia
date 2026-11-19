-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_366
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:53:03.96521+00:00
-- url     : https://prove2.me/submissions/c7f23520-fe40-4289-ab92-fd4180ab8420

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_367
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_368
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_369
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_371
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_377

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

lemma degreeUnionBranch43_370 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 27 7 degreeUnionState43_370 [7,9] = true := by
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

lemma degreeUnionBranch43_366_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 34 9 degreeUnionState43_366 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_367
  · exact degreeUnionBranch43_368
  · exact degreeUnionBranch43_369
  · exact degreeUnionBranch43_370
  · exact degreeUnionBranch43_371
  · exact degreeUnionBranch43_377

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_366_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_366_oai
