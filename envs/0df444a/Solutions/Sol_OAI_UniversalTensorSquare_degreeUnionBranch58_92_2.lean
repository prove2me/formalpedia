-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch58_92
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:42:25.935346+00:00
-- url     : https://prove2.me/submissions/a1c30f69-2d4a-4afe-b4b5-c3de9c658ed1

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_100
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_110
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_111
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_93
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_94
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_95
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_96
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_97
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_98
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_99

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

lemma degreeUnionBranch58_92_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 14 58 14 degreeHalfRegions58 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 58 ≤ 14*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_93
  · exact degreeUnionBranch58_94
  · exact degreeUnionBranch58_95
  · exact degreeUnionBranch58_96
  · exact degreeUnionBranch58_97
  · exact degreeUnionBranch58_98
  · exact degreeUnionBranch58_99
  · exact degreeUnionBranch58_100
  · exact degreeUnionBranch58_110
  · exact degreeUnionBranch58_111

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_92_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_92_oai
