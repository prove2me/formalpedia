-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_785
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:18:12.463108+00:00
-- url     : https://prove2.me/submissions/9cd84a32-0397-4a7e-98c9-028f54520499

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_786
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_787

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

lemma degreeUnionBranch62_788 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 5 degreeUnionState62_788 [5,8,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_789 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 6 degreeUnionState62_789 [6,8,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_790 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 7 degreeUnionState62_790 [7,8,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_791 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 8 degreeUnionState62_791 [8,8,11,13] = true := by
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

lemma degreeUnionBranch62_785_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 8 degreeUnionState62_785 [8,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_786
  · exact degreeUnionBranch62_787
  · exact degreeUnionBranch62_788
  · exact degreeUnionBranch62_789
  · exact degreeUnionBranch62_790
  · exact degreeUnionBranch62_791

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_785_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_785_oai
