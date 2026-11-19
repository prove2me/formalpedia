-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_371
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:53:34.00546+00:00
-- url     : https://prove2.me/submissions/614ac6e8-08c4-48a9-914b-419e06996c2a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_372

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

lemma degreeUnionBranch43_373 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 5 degreeUnionState43_373 [5,8,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_374 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 6 degreeUnionState43_374 [6,8,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_375 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 7 degreeUnionState43_375 [7,8,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_376 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 8 degreeUnionState43_376 [8,8,9] = true := by
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

lemma degreeUnionBranch43_371_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 8 degreeUnionState43_371 [8,9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_372
  · exact degreeUnionBranch43_373
  · exact degreeUnionBranch43_374
  · exact degreeUnionBranch43_375
  · exact degreeUnionBranch43_376

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_371_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_371_oai
