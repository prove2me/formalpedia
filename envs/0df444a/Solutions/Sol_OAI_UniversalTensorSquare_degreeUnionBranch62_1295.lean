-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1295
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:15:52.732616+00:00
-- url     : https://prove2.me/submissions/a92d48b9-c12f-4f09-b590-ebbbdb94a46f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1296
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1297
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1298
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1299
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1300
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1307
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1308
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1309

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

lemma degreeUnionBranch62_1295_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 37 11 degreeUnionState62_1295 [11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 37 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1296
  · exact degreeUnionBranch62_1297
  · exact degreeUnionBranch62_1298
  · exact degreeUnionBranch62_1299
  · exact degreeUnionBranch62_1300
  · exact degreeUnionBranch62_1307
  · exact degreeUnionBranch62_1308
  · exact degreeUnionBranch62_1309

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1295_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1295_oai
