-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_100
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:41:08.92785+00:00
-- url     : https://prove2.me/submissions/4ab3189f-d96b-46d8-a491-703b73dbbf5c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_101
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_102
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_107
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_108
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_109

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

lemma degreeUnionBranch58_103 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 40 6 degreeUnionState58_103 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_104 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 39 7 degreeUnionState58_104 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_105 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 38 8 degreeUnionState58_105 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_106 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 37 9 degreeUnionState58_106 [9,12] = true := by
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

lemma degreeUnionBranch58_100_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 46 12 degreeUnionState58_100 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 46 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_101
  · exact degreeUnionBranch58_102
  · exact degreeUnionBranch58_103
  · exact degreeUnionBranch58_104
  · exact degreeUnionBranch58_105
  · exact degreeUnionBranch58_106
  · exact degreeUnionBranch58_107
  · exact degreeUnionBranch58_108
  · exact degreeUnionBranch58_109

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_100_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_100_oai
