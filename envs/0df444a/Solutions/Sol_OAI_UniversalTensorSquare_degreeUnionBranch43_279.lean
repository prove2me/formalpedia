-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_279
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:40:42.71233+00:00
-- url     : https://prove2.me/submissions/78005f04-a540-4323-8f3b-f1cbc43c9b28

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

lemma degreeUnionBranch43_280 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 4 degreeUnionState43_280 [4,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_281 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 5 degreeUnionState43_281 [5,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_282 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 6 degreeUnionState43_282 [6,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_283 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 7 degreeUnionState43_283 [7,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_284 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 8 degreeUnionState43_284 [8,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_285 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 9 degreeUnionState43_285 [9,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_286 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 16 10 degreeUnionState43_286 [10,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_287 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 15 11 degreeUnionState43_287 [11,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_288 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 14 12 degreeUnionState43_288 [12,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_289 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 13 13 degreeUnionState43_289 [13,17] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_290 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 12 14 degreeUnionState43_290 [14,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_291 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 11 15 degreeUnionState43_291 [15,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_292 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 10 16 degreeUnionState43_292 [16,17] = true := by
  decide +kernel

lemma degreeUnionBranch43_293 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 9 17 degreeUnionState43_293 [17,17] = true := by
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

lemma degreeUnionBranch43_279_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 17 degreeUnionState43_279 [17] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 17 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_280
  · exact degreeUnionBranch43_281
  · exact degreeUnionBranch43_282
  · exact degreeUnionBranch43_283
  · exact degreeUnionBranch43_284
  · exact degreeUnionBranch43_285
  · exact degreeUnionBranch43_286
  · exact degreeUnionBranch43_287
  · exact degreeUnionBranch43_288
  · exact degreeUnionBranch43_289
  · exact degreeUnionBranch43_290
  · exact degreeUnionBranch43_291
  · exact degreeUnionBranch43_292
  · exact degreeUnionBranch43_293

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_279_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_279_oai
