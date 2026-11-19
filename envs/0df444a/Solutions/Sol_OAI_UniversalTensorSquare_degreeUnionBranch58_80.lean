-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:51:06.877713+00:00
-- url     : https://prove2.me/submissions/6a9bb4ca-6dbe-4fc3-8497-42a253daca38

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_87
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_88

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

lemma degreeUnionBranch58_81 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 41 4 degreeUnionState58_81 [4,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_82 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 40 5 degreeUnionState58_82 [5,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_83 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 39 6 degreeUnionState58_83 [6,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_84 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 38 7 degreeUnionState58_84 [7,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_85 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 37 8 degreeUnionState58_85 [8,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_86 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 36 9 degreeUnionState58_86 [9,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_89 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 33 12 degreeUnionState58_89 [12,13] = true := by
  decide +kernel

lemma degreeUnionBranch58_90 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 32 13 degreeUnionState58_90 [13,13] = true := by
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

lemma degreeUnionBranch58_80_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 45 13 degreeUnionState58_80 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 45 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_81
  · exact degreeUnionBranch58_82
  · exact degreeUnionBranch58_83
  · exact degreeUnionBranch58_84
  · exact degreeUnionBranch58_85
  · exact degreeUnionBranch58_86
  · exact degreeUnionBranch58_87
  · exact degreeUnionBranch58_88
  · exact degreeUnionBranch58_89
  · exact degreeUnionBranch58_90

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_80_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_80_oai
