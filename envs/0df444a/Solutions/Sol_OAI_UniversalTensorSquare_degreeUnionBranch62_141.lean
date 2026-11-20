-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_141
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:30:12.329186+00:00
-- url     : https://prove2.me/submissions/a988d29e-365d-41ac-b1e3-3ad43c3b8425

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

lemma degreeUnionBranch62_142 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 31 4 degreeUnionState62_142 [4,7,8,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_143 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 30 5 degreeUnionState62_143 [5,7,8,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_144 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 29 6 degreeUnionState62_144 [6,7,8,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_145 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 7 degreeUnionState62_145 [7,7,8,12] = true := by
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

lemma degreeUnionBranch62_141_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 7 degreeUnionState62_141 [7,8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 35 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_142
  · exact degreeUnionBranch62_143
  · exact degreeUnionBranch62_144
  · exact degreeUnionBranch62_145

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_141_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_141_oai
