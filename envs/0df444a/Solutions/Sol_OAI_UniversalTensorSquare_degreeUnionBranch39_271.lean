-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_271
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:00:43.260568+00:00
-- url     : https://prove2.me/submissions/fac129bc-8621-427a-81e8-39ccc603e250

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_272 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 23 3 degreeUnionState39_272 [3,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_273 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 22 4 degreeUnionState39_273 [4,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_274 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 21 5 degreeUnionState39_274 [5,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_275 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 20 6 degreeUnionState39_275 [6,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_276 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 19 7 degreeUnionState39_276 [7,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_277 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 18 8 degreeUnionState39_277 [8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_278 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 17 9 degreeUnionState39_278 [9,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_279 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 16 10 degreeUnionState39_279 [10,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_280 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 15 11 degreeUnionState39_280 [11,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_281 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 14 12 degreeUnionState39_281 [12,13] = true := by
  decide +kernel

lemma degreeUnionBranch39_282 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 13 13 degreeUnionState39_282 [13,13] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_271_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 26 13 degreeUnionState39_271 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 13 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_272
  · exact degreeUnionBranch39_273
  · exact degreeUnionBranch39_274
  · exact degreeUnionBranch39_275
  · exact degreeUnionBranch39_276
  · exact degreeUnionBranch39_277
  · exact degreeUnionBranch39_278
  · exact degreeUnionBranch39_279
  · exact degreeUnionBranch39_280
  · exact degreeUnionBranch39_281
  · exact degreeUnionBranch39_282

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_271_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_271_oai
