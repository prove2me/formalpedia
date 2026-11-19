-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_22
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:32.615232+00:00
-- url     : https://prove2.me/submissions/30a649d7-3538-464e-baad-bf71d0b90352

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_23
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_24
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_25
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_26
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_27
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_28

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

lemma degreeUnionBranch43_22_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 33 10 degreeUnionState43_22 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_23
  · exact degreeUnionBranch43_24
  · exact degreeUnionBranch43_25
  · exact degreeUnionBranch43_26
  · exact degreeUnionBranch43_27
  · exact degreeUnionBranch43_28

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_22_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_22_oai
