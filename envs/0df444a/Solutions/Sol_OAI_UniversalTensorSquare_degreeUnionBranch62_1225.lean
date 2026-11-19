-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1225
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:57:32.550864+00:00
-- url     : https://prove2.me/submissions/1ed2860c-2269-4eaa-8260-f17310f6972f

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

lemma degreeUnionBranch62_1226 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 3 degreeUnionState62_1226 [3,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1227 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 4 degreeUnionState62_1227 [4,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1228 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 5 degreeUnionState62_1228 [5,13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_1229 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 6 degreeUnionState62_1229 [6,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1230 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 7 degreeUnionState62_1230 [7,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1231 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 28 8 degreeUnionState62_1231 [8,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1232 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 27 9 degreeUnionState62_1232 [9,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1233 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 26 10 degreeUnionState62_1233 [10,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1234 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 25 11 degreeUnionState62_1234 [11,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1235 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 24 12 degreeUnionState62_1235 [12,13,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1236 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 23 13 degreeUnionState62_1236 [13,13,13] = true := by
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

lemma degreeUnionBranch62_1225_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 36 13 degreeUnionState62_1225 [13,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 36 ≤ 12*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1226
  · exact degreeUnionBranch62_1227
  · exact degreeUnionBranch62_1228
  · exact degreeUnionBranch62_1229
  · exact degreeUnionBranch62_1230
  · exact degreeUnionBranch62_1231
  · exact degreeUnionBranch62_1232
  · exact degreeUnionBranch62_1233
  · exact degreeUnionBranch62_1234
  · exact degreeUnionBranch62_1235
  · exact degreeUnionBranch62_1236

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1225_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1225_oai
