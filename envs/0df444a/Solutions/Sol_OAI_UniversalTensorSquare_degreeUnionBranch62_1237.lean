-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1237
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:25:18.30504+00:00
-- url     : https://prove2.me/submissions/6ee66919-eac0-4a08-b4a4-76ad6d8da1d6

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1238
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1239
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1240
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1241
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1242
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1254
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1274
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1295
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1310
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1321
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1322

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

lemma degreeUnionBranch62_1237_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 48 14 degreeUnionState62_1237 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1238
  · exact degreeUnionBranch62_1239
  · exact degreeUnionBranch62_1240
  · exact degreeUnionBranch62_1241
  · exact degreeUnionBranch62_1242
  · exact degreeUnionBranch62_1254
  · exact degreeUnionBranch62_1274
  · exact degreeUnionBranch62_1295
  · exact degreeUnionBranch62_1310
  · exact degreeUnionBranch62_1321
  · exact degreeUnionBranch62_1322

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1237_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1237_oai
