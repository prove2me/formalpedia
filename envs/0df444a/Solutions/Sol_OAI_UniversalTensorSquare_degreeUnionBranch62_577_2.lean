-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch62_577
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:43:28.529168+00:00
-- url     : https://prove2.me/submissions/7019a9b8-03f6-44bc-a2d5-1cdfc0637a0f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_578
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_579
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_580
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_581
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_582
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_583
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_584
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_585
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_586

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

lemma degreeUnionBranch62_577_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 11 degreeUnionState62_577 [11,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 11 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_578
  · exact degreeUnionBranch62_579
  · exact degreeUnionBranch62_580
  · exact degreeUnionBranch62_581
  · exact degreeUnionBranch62_582
  · exact degreeUnionBranch62_583
  · exact degreeUnionBranch62_584
  · exact degreeUnionBranch62_585
  · exact degreeUnionBranch62_586

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_577_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_577_oai
