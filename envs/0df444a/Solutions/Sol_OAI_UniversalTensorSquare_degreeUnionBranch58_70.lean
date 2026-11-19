-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_70
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:47:03.827906+00:00
-- url     : https://prove2.me/submissions/341ae96d-44e6-4de7-91a0-02c7bf055bf6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_77

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

lemma degreeUnionBranch58_71 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 42 4 degreeUnionState58_71 [4,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_72 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 41 5 degreeUnionState58_72 [5,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_73 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 40 6 degreeUnionState58_73 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_74 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 39 7 degreeUnionState58_74 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_75 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 38 8 degreeUnionState58_75 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_76 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 37 9 degreeUnionState58_76 [9,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_78 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 35 11 degreeUnionState58_78 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_79 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 34 12 degreeUnionState58_79 [12,12] = true := by
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

lemma degreeUnionBranch58_70_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 46 12 degreeUnionState58_70 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 46 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_71
  · exact degreeUnionBranch58_72
  · exact degreeUnionBranch58_73
  · exact degreeUnionBranch58_74
  · exact degreeUnionBranch58_75
  · exact degreeUnionBranch58_76
  · exact degreeUnionBranch58_77
  · exact degreeUnionBranch58_78
  · exact degreeUnionBranch58_79

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_70_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_70_oai
