-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch58_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:41:59.648869+00:00
-- url     : https://prove2.me/submissions/a4003031-87da-438f-a651-649106ed2fd6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_13
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_14
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_15
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_18
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_19
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_20
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_35
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_50

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_16 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 50 8 degreeUnionState58_16 [8] = true := by
  decide +kernel

lemma degreeUnionBranch58_17 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 49 9 degreeUnionState58_17 [9] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_12_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 58 14 degreeHalfRegions58 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 58 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_13
  · exact degreeUnionBranch58_14
  · exact degreeUnionBranch58_15
  · exact degreeUnionBranch58_16
  · exact degreeUnionBranch58_17
  · exact degreeUnionBranch58_18
  · exact degreeUnionBranch58_19
  · exact degreeUnionBranch58_20
  · exact degreeUnionBranch58_35
  · exact degreeUnionBranch58_50

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_12_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_12_oai
