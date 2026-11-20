-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_1178
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:42:47.161228+00:00
-- url     : https://prove2.me/submissions/cc34c800-f1f9-4185-ba68-49e31206f47f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1179
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1180
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1181
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1182
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1183
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1184
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1185
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1186

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

lemma degreeUnionBranch62_1178_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 10 degreeUnionState62_1178 [10,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1179
  · exact degreeUnionBranch62_1180
  · exact degreeUnionBranch62_1181
  · exact degreeUnionBranch62_1182
  · exact degreeUnionBranch62_1183
  · exact degreeUnionBranch62_1184
  · exact degreeUnionBranch62_1185
  · exact degreeUnionBranch62_1186

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1178_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1178_oai
