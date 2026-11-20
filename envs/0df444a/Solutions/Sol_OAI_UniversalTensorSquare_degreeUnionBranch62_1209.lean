-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1209
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:42:30.932734+00:00
-- url     : https://prove2.me/submissions/e5326930-4374-4c1f-ae13-2670a74b9b1c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1210
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1211
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1212
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1213
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1214
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1221
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1222
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1223
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1224

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

lemma degreeUnionBranch62_1209_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 37 12 degreeUnionState62_1209 [12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 37 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1210
  · exact degreeUnionBranch62_1211
  · exact degreeUnionBranch62_1212
  · exact degreeUnionBranch62_1213
  · exact degreeUnionBranch62_1214
  · exact degreeUnionBranch62_1221
  · exact degreeUnionBranch62_1222
  · exact degreeUnionBranch62_1223
  · exact degreeUnionBranch62_1224

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1209_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1209_oai
