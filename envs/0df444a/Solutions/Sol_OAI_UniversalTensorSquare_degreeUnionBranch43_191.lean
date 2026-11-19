-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_191
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:23:43.703164+00:00
-- url     : https://prove2.me/submissions/e2a80404-8fb4-4359-bb21-5b144418e727

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_192
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_193
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_194
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_195
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_196

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

lemma degreeUnionBranch43_191_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 34 9 degreeUnionState43_191 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_192
  · exact degreeUnionBranch43_193
  · exact degreeUnionBranch43_194
  · exact degreeUnionBranch43_195
  · exact degreeUnionBranch43_196

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_191_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_191_oai
