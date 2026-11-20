-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1192
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:30:40.517178+00:00
-- url     : https://prove2.me/submissions/276852b7-c082-43c2-b694-88882f2fc2f8

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1193
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1194

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

lemma degreeUnionBranch62_1195 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 5 degreeUnionState62_1195 [5,8,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1196 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 6 degreeUnionState62_1196 [6,8,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1197 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 7 degreeUnionState62_1197 [7,8,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1198 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 8 degreeUnionState62_1198 [8,8,11,13] = true := by
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

lemma degreeUnionBranch62_1192_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 8 degreeUnionState62_1192 [8,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1193
  · exact degreeUnionBranch62_1194
  · exact degreeUnionBranch62_1195
  · exact degreeUnionBranch62_1196
  · exact degreeUnionBranch62_1197
  · exact degreeUnionBranch62_1198

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1192_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1192_oai
