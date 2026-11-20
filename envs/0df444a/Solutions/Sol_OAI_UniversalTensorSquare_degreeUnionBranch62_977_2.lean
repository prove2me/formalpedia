-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_977
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:45:55.596174+00:00
-- url     : https://prove2.me/submissions/f8e07fd9-b0a8-4926-a099-f917c7c28e2f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_978
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_979
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_980
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_981
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_982
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_984
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_993

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

lemma degreeUnionBranch62_983 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 9 degreeUnionState62_983 [9,11,11] = true := by
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

lemma degreeUnionBranch62_977_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 11 degreeUnionState62_977 [11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 40 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_978
  · exact degreeUnionBranch62_979
  · exact degreeUnionBranch62_980
  · exact degreeUnionBranch62_981
  · exact degreeUnionBranch62_982
  · exact degreeUnionBranch62_983
  · exact degreeUnionBranch62_984
  · exact degreeUnionBranch62_993

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_977_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_977_oai
