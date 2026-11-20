-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_662
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:32:50.416354+00:00
-- url     : https://prove2.me/submissions/f48dea10-b245-4a74-b68d-5d291851de93

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_663

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

lemma degreeUnionBranch62_664 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 4 degreeUnionState62_664 [4,9,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_665 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 5 degreeUnionState62_665 [5,9,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_666 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 6 degreeUnionState62_666 [6,9,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_667 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 7 degreeUnionState62_667 [7,9,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_668 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 8 degreeUnionState62_668 [8,9,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_669 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 9 degreeUnionState62_669 [9,9,11,12] = true := by
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

lemma degreeUnionBranch62_662_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 9 degreeUnionState62_662 [9,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_663
  · exact degreeUnionBranch62_664
  · exact degreeUnionBranch62_665
  · exact degreeUnionBranch62_666
  · exact degreeUnionBranch62_667
  · exact degreeUnionBranch62_668
  · exact degreeUnionBranch62_669

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_662_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_662_oai
