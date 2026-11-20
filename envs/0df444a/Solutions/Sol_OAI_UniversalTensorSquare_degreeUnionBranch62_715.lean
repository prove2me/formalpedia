-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_715
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:54:47.002889+00:00
-- url     : https://prove2.me/submissions/e789dd9b-ca66-4a86-999e-81e4b8ea1174

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_720

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

lemma degreeUnionBranch62_716 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 4 degreeUnionState62_716 [4,8,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_717 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 5 degreeUnionState62_717 [5,8,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_718 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 6 degreeUnionState62_718 [6,8,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_719 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 7 degreeUnionState62_719 [7,8,13] = true := by
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

lemma degreeUnionBranch62_715_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 8 degreeUnionState62_715 [8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 41 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_716
  · exact degreeUnionBranch62_717
  · exact degreeUnionBranch62_718
  · exact degreeUnionBranch62_719
  · exact degreeUnionBranch62_720

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_715_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_715_oai
