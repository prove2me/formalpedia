-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:32:16.672193+00:00
-- url     : https://prove2.me/submissions/b86548b0-10d9-4a63-928e-b5d8302dbaa9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_38
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_39
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_40
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_41
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_42
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_43
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_44
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_45
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_46
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_47

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

lemma degreeUnionBranch62_37_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 48 14 degreeUnionState62_37 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_38
  · exact degreeUnionBranch62_39
  · exact degreeUnionBranch62_40
  · exact degreeUnionBranch62_41
  · exact degreeUnionBranch62_42
  · exact degreeUnionBranch62_43
  · exact degreeUnionBranch62_44
  · exact degreeUnionBranch62_45
  · exact degreeUnionBranch62_46
  · exact degreeUnionBranch62_47

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_37_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_37_oai
