-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1187
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:34:51.787336+00:00
-- url     : https://prove2.me/submissions/b3ba067c-dc5f-46b4-9b19-b330d834e3c9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1188
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1189
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1190
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1191
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1192
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1199
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1207
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1208

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

lemma degreeUnionBranch62_1187_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 38 11 degreeUnionState62_1187 [11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 38 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1188
  · exact degreeUnionBranch62_1189
  · exact degreeUnionBranch62_1190
  · exact degreeUnionBranch62_1191
  · exact degreeUnionBranch62_1192
  · exact degreeUnionBranch62_1199
  · exact degreeUnionBranch62_1207
  · exact degreeUnionBranch62_1208

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1187_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1187_oai
