-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_540
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:49:19.778833+00:00
-- url     : https://prove2.me/submissions/d9afb09b-3a2d-4d74-8cfa-3d5afd3a8bfc

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_546
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_561

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

lemma degreeUnionBranch62_541 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 46 5 degreeUnionState62_541 [5,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_542 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 45 6 degreeUnionState62_542 [6,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_543 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 44 7 degreeUnionState62_543 [7,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_544 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 43 8 degreeUnionState62_544 [8,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_545 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 9 degreeUnionState62_545 [9,11] = true := by
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

lemma degreeUnionBranch62_540_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 51 11 degreeUnionState62_540 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 51 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_541
  · exact degreeUnionBranch62_542
  · exact degreeUnionBranch62_543
  · exact degreeUnionBranch62_544
  · exact degreeUnionBranch62_545
  · exact degreeUnionBranch62_546
  · exact degreeUnionBranch62_561

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_540_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_540_oai
