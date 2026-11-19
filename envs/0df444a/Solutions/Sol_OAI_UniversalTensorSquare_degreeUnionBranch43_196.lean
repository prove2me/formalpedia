-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_196
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:13.821113+00:00
-- url     : https://prove2.me/submissions/45359940-3a3c-4736-a9d1-51f485cd1cd4

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_197
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_198
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_199
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_200

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

lemma degreeUnionBranch43_201 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 8 degreeUnionState43_201 [8,9,9] = true := by
  decide +kernel

lemma degreeUnionBranch43_202 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 16 9 degreeUnionState43_202 [9,9,9] = true := by
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

lemma degreeUnionBranch43_196_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 9 degreeUnionState43_196 [9,9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_197
  · exact degreeUnionBranch43_198
  · exact degreeUnionBranch43_199
  · exact degreeUnionBranch43_200
  · exact degreeUnionBranch43_201
  · exact degreeUnionBranch43_202

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_196_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_196_oai
