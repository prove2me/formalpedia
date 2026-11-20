-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_969
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:54:18.637292+00:00
-- url     : https://prove2.me/submissions/99df9aa7-cf68-43f7-b770-575cb96683fb

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_970
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_971
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_972
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_976

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

lemma degreeUnionBranch62_973 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 7 degreeUnionState62_973 [7,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_974 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 8 degreeUnionState62_974 [8,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_975 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 9 degreeUnionState62_975 [9,10,11] = true := by
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

lemma degreeUnionBranch62_969_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 41 10 degreeUnionState62_969 [10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 41 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_970
  · exact degreeUnionBranch62_971
  · exact degreeUnionBranch62_972
  · exact degreeUnionBranch62_973
  · exact degreeUnionBranch62_974
  · exact degreeUnionBranch62_975
  · exact degreeUnionBranch62_976

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_969_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_969_oai
