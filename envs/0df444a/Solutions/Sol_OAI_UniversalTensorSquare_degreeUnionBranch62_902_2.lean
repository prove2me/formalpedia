-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_902
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:45:33.821646+00:00
-- url     : https://prove2.me/submissions/e0f69ccf-9129-415c-a810-5a37ae324a9b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_903
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_904
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_905
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_906
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_912
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_919
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_920
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_921

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

lemma degreeUnionBranch62_902_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 37 11 degreeUnionState62_902 [11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 37 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_903
  · exact degreeUnionBranch62_904
  · exact degreeUnionBranch62_905
  · exact degreeUnionBranch62_906
  · exact degreeUnionBranch62_912
  · exact degreeUnionBranch62_919
  · exact degreeUnionBranch62_920
  · exact degreeUnionBranch62_921

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_902_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_902_oai
