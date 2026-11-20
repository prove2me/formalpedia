-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_99
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:00:35.155671+00:00
-- url     : https://prove2.me/submissions/3c31dadc-866f-4ccd-800e-0c48490f2708

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_100
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_106

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_101 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 5 degreeUnionState62_101 [5,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_102 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 6 degreeUnionState62_102 [6,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_103 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 7 degreeUnionState62_103 [7,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_104 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 8 degreeUnionState62_104 [8,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_105 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 9 degreeUnionState62_105 [9,10,10,11] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_99_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 10 degreeUnionState62_99 [10,10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_100
  · exact degreeUnionBranch62_101
  · exact degreeUnionBranch62_102
  · exact degreeUnionBranch62_103
  · exact degreeUnionBranch62_104
  · exact degreeUnionBranch62_105
  · exact degreeUnionBranch62_106

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_99_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_99_oai
