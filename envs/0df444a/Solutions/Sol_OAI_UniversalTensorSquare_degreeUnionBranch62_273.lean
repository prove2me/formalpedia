-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_273
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:31:25.099569+00:00
-- url     : https://prove2.me/submissions/bb915e59-4436-4130-9cc3-966b0e744f21

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

lemma degreeUnionBranch62_274 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 30 4 degreeUnionState62_274 [4,7,8,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_275 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 29 5 degreeUnionState62_275 [5,7,8,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_276 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 6 degreeUnionState62_276 [6,7,8,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_277 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 7 degreeUnionState62_277 [7,7,8,13] = true := by
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

lemma degreeUnionBranch62_273_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 7 degreeUnionState62_273 [7,8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_274
  · exact degreeUnionBranch62_275
  · exact degreeUnionBranch62_276
  · exact degreeUnionBranch62_277

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_273_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_273_oai
