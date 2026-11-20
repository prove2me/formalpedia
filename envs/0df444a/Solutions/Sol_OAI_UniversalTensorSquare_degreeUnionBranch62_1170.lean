-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1170
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:21:33.980215+00:00
-- url     : https://prove2.me/submissions/df7673be-2201-4f29-953c-55aaf9cb95c9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1171
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1172
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1173

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

lemma degreeUnionBranch62_1174 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 6 degreeUnionState62_1174 [6,9,10,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1175 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 7 degreeUnionState62_1175 [7,9,10,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1176 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 8 degreeUnionState62_1176 [8,9,10,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1177 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 21 9 degreeUnionState62_1177 [9,9,10,13] = true := by
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

lemma degreeUnionBranch62_1170_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 9 degreeUnionState62_1170 [9,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1171
  · exact degreeUnionBranch62_1172
  · exact degreeUnionBranch62_1173
  · exact degreeUnionBranch62_1174
  · exact degreeUnionBranch62_1175
  · exact degreeUnionBranch62_1176
  · exact degreeUnionBranch62_1177

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1170_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1170_oai
