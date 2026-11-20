-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_587
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:05:09.815725+00:00
-- url     : https://prove2.me/submissions/2a000ad1-3a84-4751-9cb3-37fc0df4c494

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_588
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_589
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_590
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_591
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_602
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_620
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_647
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_680

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

lemma degreeUnionBranch62_587_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 50 12 degreeUnionState62_587 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_588
  · exact degreeUnionBranch62_589
  · exact degreeUnionBranch62_590
  · exact degreeUnionBranch62_591
  · exact degreeUnionBranch62_602
  · exact degreeUnionBranch62_620
  · exact degreeUnionBranch62_647
  · exact degreeUnionBranch62_680

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_587_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_587_oai
