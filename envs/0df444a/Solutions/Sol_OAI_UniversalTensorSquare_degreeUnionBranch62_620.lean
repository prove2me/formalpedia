-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_620
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:21:49.851927+00:00
-- url     : https://prove2.me/submissions/725832bd-b850-4e38-8cdc-7edb8b5929f2

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_621
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_622
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_623
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_625
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_631
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_638

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

lemma degreeUnionBranch62_624 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 7 degreeUnionState62_624 [7,10,12] = true := by
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

lemma degreeUnionBranch62_620_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 10 degreeUnionState62_620 [10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 40 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_621
  · exact degreeUnionBranch62_622
  · exact degreeUnionBranch62_623
  · exact degreeUnionBranch62_624
  · exact degreeUnionBranch62_625
  · exact degreeUnionBranch62_631
  · exact degreeUnionBranch62_638

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_620_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_620_oai
