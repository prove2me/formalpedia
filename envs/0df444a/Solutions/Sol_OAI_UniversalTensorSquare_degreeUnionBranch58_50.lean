-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:46:33.301495+00:00
-- url     : https://prove2.me/submissions/41f55a49-7c06-4e5f-b8ba-62fa0ef71fe1

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_57

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

lemma degreeUnionBranch58_51 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 40 4 degreeUnionState58_51 [4,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_52 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 39 5 degreeUnionState58_52 [5,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_53 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 38 6 degreeUnionState58_53 [6,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_54 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 37 7 degreeUnionState58_54 [7,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_55 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 36 8 degreeUnionState58_55 [8,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_56 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 35 9 degreeUnionState58_56 [9,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_58 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 33 11 degreeUnionState58_58 [11,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_59 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 32 12 degreeUnionState58_59 [12,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_60 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 31 13 degreeUnionState58_60 [13,14] = true := by
  decide +kernel

lemma degreeUnionBranch58_61 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 30 14 degreeUnionState58_61 [14,14] = true := by
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

lemma degreeUnionBranch58_50_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 44 14 degreeUnionState58_50 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 44 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_51
  · exact degreeUnionBranch58_52
  · exact degreeUnionBranch58_53
  · exact degreeUnionBranch58_54
  · exact degreeUnionBranch58_55
  · exact degreeUnionBranch58_56
  · exact degreeUnionBranch58_57
  · exact degreeUnionBranch58_58
  · exact degreeUnionBranch58_59
  · exact degreeUnionBranch58_60
  · exact degreeUnionBranch58_61

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_50_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_50_oai
