-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:53:27.954081+00:00
-- url     : https://prove2.me/submissions/6e2636ea-aa80-4c63-ae59-5d37dc6de974

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_38
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_39
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_40
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_41
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_42
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_43
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_44
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_45

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

lemma degreeUnionBranch43_37_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 31 12 degreeUnionState43_37 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_38
  · exact degreeUnionBranch43_39
  · exact degreeUnionBranch43_40
  · exact degreeUnionBranch43_41
  · exact degreeUnionBranch43_42
  · exact degreeUnionBranch43_43
  · exact degreeUnionBranch43_44
  · exact degreeUnionBranch43_45

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_37_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_37_oai
