-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_710
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:54:40.444325+00:00
-- url     : https://prove2.me/submissions/7b5f9e33-d3f2-4ced-9d0a-840adda10d79

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

lemma degreeUnionBranch62_711 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 4 degreeUnionState62_711 [4,7,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_712 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 5 degreeUnionState62_712 [5,7,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_713 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 6 degreeUnionState62_713 [6,7,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_714 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 7 degreeUnionState62_714 [7,7,13] = true := by
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

lemma degreeUnionBranch62_710_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 7 degreeUnionState62_710 [7,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 42 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_711
  · exact degreeUnionBranch62_712
  · exact degreeUnionBranch62_713
  · exact degreeUnionBranch62_714

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_710_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_710_oai
