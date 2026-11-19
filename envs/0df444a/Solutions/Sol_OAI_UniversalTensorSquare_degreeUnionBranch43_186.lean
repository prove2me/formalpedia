-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_186
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:23:37.963266+00:00
-- url     : https://prove2.me/submissions/87bbcd17-a13f-44a4-a3ad-c2d2c59b7e10

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_187 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 30 5 degreeUnionState43_187 [5,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_188 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 29 6 degreeUnionState43_188 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_189 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 28 7 degreeUnionState43_189 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch43_190 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 27 8 degreeUnionState43_190 [8,8] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_186_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 35 8 degreeUnionState43_186 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_187
  · exact degreeUnionBranch43_188
  · exact degreeUnionBranch43_189
  · exact degreeUnionBranch43_190

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_186_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_186_oai
