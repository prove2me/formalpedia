-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_1310
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:44:42.528609+00:00
-- url     : https://prove2.me/submissions/39c22565-8ccf-4f47-9ccd-382e782c7411

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1311
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1312
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1313
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1314
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1315
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1316
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1317
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1318
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1319
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1320

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

lemma degreeUnionBranch62_1310_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 36 12 degreeUnionState62_1310 [12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 36 ≤ 12*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1311
  · exact degreeUnionBranch62_1312
  · exact degreeUnionBranch62_1313
  · exact degreeUnionBranch62_1314
  · exact degreeUnionBranch62_1315
  · exact degreeUnionBranch62_1316
  · exact degreeUnionBranch62_1317
  · exact degreeUnionBranch62_1318
  · exact degreeUnionBranch62_1319
  · exact degreeUnionBranch62_1320

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1310_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1310_oai
