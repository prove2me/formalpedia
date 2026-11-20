-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_656
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:32:43.623454+00:00
-- url     : https://prove2.me/submissions/1fbe1e0d-3ada-429e-b62b-fed604b179eb

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

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

lemma degreeUnionBranch62_657 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 4 degreeUnionState62_657 [4,8,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_658 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 5 degreeUnionState62_658 [5,8,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_659 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 6 degreeUnionState62_659 [6,8,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_660 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 7 degreeUnionState62_660 [7,8,11,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_661 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 8 degreeUnionState62_661 [8,8,11,12] = true := by
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

lemma degreeUnionBranch62_656_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 8 degreeUnionState62_656 [8,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_657
  · exact degreeUnionBranch62_658
  · exact degreeUnionBranch62_659
  · exact degreeUnionBranch62_660
  · exact degreeUnionBranch62_661

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_656_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_656_oai
