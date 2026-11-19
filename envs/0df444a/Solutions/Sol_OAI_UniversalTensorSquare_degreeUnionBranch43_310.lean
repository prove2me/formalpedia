-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_310
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:44:06.066512+00:00
-- url     : https://prove2.me/submissions/02df8cba-f7a5-443a-97ad-fa00527332e5

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

lemma degreeUnionBranch43_311 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 3 degreeUnionState43_311 [3,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_312 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 4 degreeUnionState43_312 [4,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_313 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 5 degreeUnionState43_313 [5,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_314 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 6 degreeUnionState43_314 [6,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_315 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 7 degreeUnionState43_315 [7,19] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_316 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 16 8 degreeUnionState43_316 [8,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_317 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 15 9 degreeUnionState43_317 [9,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_318 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 14 10 degreeUnionState43_318 [10,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_319 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 13 11 degreeUnionState43_319 [11,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_320 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 12 12 degreeUnionState43_320 [12,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_321 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 11 13 degreeUnionState43_321 [13,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_322 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 10 14 degreeUnionState43_322 [14,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_323 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 9 15 degreeUnionState43_323 [15,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_324 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 8 16 degreeUnionState43_324 [16,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_325 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 7 17 degreeUnionState43_325 [17,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_326 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 6 18 degreeUnionState43_326 [18,19] = true := by
  decide +kernel

lemma degreeUnionBranch43_327 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 5 19 degreeUnionState43_327 [19,19] = true := by
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

lemma degreeUnionBranch43_310_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 19 degreeUnionState43_310 [19] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 19 at hb
  change 24 ≤ 8*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_311
  · exact degreeUnionBranch43_312
  · exact degreeUnionBranch43_313
  · exact degreeUnionBranch43_314
  · exact degreeUnionBranch43_315
  · exact degreeUnionBranch43_316
  · exact degreeUnionBranch43_317
  · exact degreeUnionBranch43_318
  · exact degreeUnionBranch43_319
  · exact degreeUnionBranch43_320
  · exact degreeUnionBranch43_321
  · exact degreeUnionBranch43_322
  · exact degreeUnionBranch43_323
  · exact degreeUnionBranch43_324
  · exact degreeUnionBranch43_325
  · exact degreeUnionBranch43_326
  · exact degreeUnionBranch43_327

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_310_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_310_oai
