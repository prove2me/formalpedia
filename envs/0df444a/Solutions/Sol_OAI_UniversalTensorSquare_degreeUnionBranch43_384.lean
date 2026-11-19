-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_384
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:54:09.631621+00:00
-- url     : https://prove2.me/submissions/63ba6a90-55b6-4d90-b152-44580e0a0c58

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_385
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_386
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_387
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_388
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_389
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_390
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_391

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_384_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 33 10 degreeUnionState43_384 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_385
  · exact degreeUnionBranch43_386
  · exact degreeUnionBranch43_387
  · exact degreeUnionBranch43_388
  · exact degreeUnionBranch43_389
  · exact degreeUnionBranch43_390
  · exact degreeUnionBranch43_391

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_384_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_384_oai
