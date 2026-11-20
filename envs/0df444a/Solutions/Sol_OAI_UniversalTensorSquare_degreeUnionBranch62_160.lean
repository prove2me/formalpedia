-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_160
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:33:41.377188+00:00
-- url     : https://prove2.me/submissions/182fdda7-123d-4f02-afc4-17dc68f145b4

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_161

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

lemma degreeUnionBranch62_162 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 5 degreeUnionState62_162 [5,8,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_163 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 6 degreeUnionState62_163 [6,8,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_164 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 7 degreeUnionState62_164 [7,8,9,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_165 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 8 degreeUnionState62_165 [8,8,9,12] = true := by
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

lemma degreeUnionBranch62_160_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 8 degreeUnionState62_160 [8,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_161
  · exact degreeUnionBranch62_162
  · exact degreeUnionBranch62_163
  · exact degreeUnionBranch62_164
  · exact degreeUnionBranch62_165

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_160_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_160_oai
