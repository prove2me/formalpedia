-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_18
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:26:06.982465+00:00
-- url     : https://prove2.me/submissions/f66dd472-8c6f-4398-bc33-14f0b3746f0c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_19
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_20
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_21
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_22
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_23
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_24
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_25
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_26

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

lemma degreeUnionBranch62_18_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 50 12 degreeUnionState62_18 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_19
  · exact degreeUnionBranch62_20
  · exact degreeUnionBranch62_21
  · exact degreeUnionBranch62_22
  · exact degreeUnionBranch62_23
  · exact degreeUnionBranch62_24
  · exact degreeUnionBranch62_25
  · exact degreeUnionBranch62_26

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_18_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_18_oai
