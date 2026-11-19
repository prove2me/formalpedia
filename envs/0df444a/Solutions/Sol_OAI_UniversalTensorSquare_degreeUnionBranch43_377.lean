-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_377
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:53:45.720874+00:00
-- url     : https://prove2.me/submissions/b659b55a-4d89-4817-9308-bda81d0c1dbc

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_378
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_379

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

lemma degreeUnionBranch43_380 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 6 degreeUnionState43_380 [6,9,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_381 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 7 degreeUnionState43_381 [7,9,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_382 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 8 degreeUnionState43_382 [8,9,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_383 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 16 9 degreeUnionState43_383 [9,9,9] = true := by
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

lemma degreeUnionBranch43_377_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 9 degreeUnionState43_377 [9,9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_378
  · exact degreeUnionBranch43_379
  · exact degreeUnionBranch43_380
  · exact degreeUnionBranch43_381
  · exact degreeUnionBranch43_382
  · exact degreeUnionBranch43_383

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_377_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_377_oai
