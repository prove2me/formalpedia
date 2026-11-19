-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:42:03.132886+00:00
-- url     : https://prove2.me/submissions/c0527b0c-999d-4b91-8f78-355ed6936d5c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_26 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 9 33 4 degreeUnionState58_26 [4,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_27 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 9 32 5 degreeUnionState58_27 [5,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_28 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 9 31 6 degreeUnionState58_28 [6,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_29 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 9 30 7 degreeUnionState58_29 [7,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_30 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 9 29 8 degreeUnionState58_30 [8,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_31 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 9 28 9 degreeUnionState58_31 [9,9,12] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_25_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 37 9 degreeUnionState58_25 [9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 37 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_26
  · exact degreeUnionBranch58_27
  · exact degreeUnionBranch58_28
  · exact degreeUnionBranch58_29
  · exact degreeUnionBranch58_30
  · exact degreeUnionBranch58_31

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_25_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_25_oai
