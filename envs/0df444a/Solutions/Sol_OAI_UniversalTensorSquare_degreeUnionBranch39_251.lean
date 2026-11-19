-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_251
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:00:31.785951+00:00
-- url     : https://prove2.me/submissions/1571a662-3666-4f03-856f-b8d31360c0ea

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

lemma degreeUnionBranch39_252 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 24 4 degreeUnionState39_252 [4,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_253 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 23 5 degreeUnionState39_253 [5,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_254 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 22 6 degreeUnionState39_254 [6,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_255 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 21 7 degreeUnionState39_255 [7,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_256 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 20 8 degreeUnionState39_256 [8,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_257 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 19 9 degreeUnionState39_257 [9,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_258 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 18 10 degreeUnionState39_258 [10,11] = true := by
  decide +kernel

lemma degreeUnionBranch39_259 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 17 11 degreeUnionState39_259 [11,11] = true := by
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

lemma degreeUnionBranch39_251_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 28 11 degreeUnionState39_251 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 28 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_252
  · exact degreeUnionBranch39_253
  · exact degreeUnionBranch39_254
  · exact degreeUnionBranch39_255
  · exact degreeUnionBranch39_256
  · exact degreeUnionBranch39_257
  · exact degreeUnionBranch39_258
  · exact degreeUnionBranch39_259

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_251_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_251_oai
