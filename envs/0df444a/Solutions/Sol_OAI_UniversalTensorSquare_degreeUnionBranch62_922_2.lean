-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_922
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:45:41.620071+00:00
-- url     : https://prove2.me/submissions/f3888589-40af-4a3c-b9de-ce1631870c3b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_923
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_924
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_925
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_926
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_927
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_928
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_929
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_930
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_931

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

lemma degreeUnionBranch62_922_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 12 degreeUnionState62_922 [12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 36 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_923
  · exact degreeUnionBranch62_924
  · exact degreeUnionBranch62_925
  · exact degreeUnionBranch62_926
  · exact degreeUnionBranch62_927
  · exact degreeUnionBranch62_928
  · exact degreeUnionBranch62_929
  · exact degreeUnionBranch62_930
  · exact degreeUnionBranch62_931

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_922_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_922_oai
