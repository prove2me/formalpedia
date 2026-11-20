-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_568
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:59:30.043178+00:00
-- url     : https://prove2.me/submissions/069cc846-db49-4796-939c-202fffc53979

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_569
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_570
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_571
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_576

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

lemma degreeUnionBranch62_572 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 6 degreeUnionState62_572 [6,10,11,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_573 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 7 degreeUnionState62_573 [7,10,11,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_574 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 8 degreeUnionState62_574 [8,10,11,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_575 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 9 degreeUnionState62_575 [9,10,11,11] = true := by
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

lemma degreeUnionBranch62_568_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 10 degreeUnionState62_568 [10,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_569
  · exact degreeUnionBranch62_570
  · exact degreeUnionBranch62_571
  · exact degreeUnionBranch62_572
  · exact degreeUnionBranch62_573
  · exact degreeUnionBranch62_574
  · exact degreeUnionBranch62_575
  · exact degreeUnionBranch62_576

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_568_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_568_oai
