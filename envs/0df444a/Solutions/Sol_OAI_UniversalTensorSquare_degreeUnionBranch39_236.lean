-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:00:18.177194+00:00
-- url     : https://prove2.me/submissions/00aa55be-b77c-4b5f-9c5f-b76c6c532e04

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

lemma degreeUnionBranch39_237 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 26 4 degreeUnionState39_237 [4,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_238 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 25 5 degreeUnionState39_238 [5,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_239 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 24 6 degreeUnionState39_239 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_240 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 23 7 degreeUnionState39_240 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_241 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 22 8 degreeUnionState39_241 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch39_242 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 21 9 degreeUnionState39_242 [9,9] = true := by
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

lemma degreeUnionBranch39_236_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 30 9 degreeUnionState39_236 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_237
  · exact degreeUnionBranch39_238
  · exact degreeUnionBranch39_239
  · exact degreeUnionBranch39_240
  · exact degreeUnionBranch39_241
  · exact degreeUnionBranch39_242

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_236_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_236_oai
