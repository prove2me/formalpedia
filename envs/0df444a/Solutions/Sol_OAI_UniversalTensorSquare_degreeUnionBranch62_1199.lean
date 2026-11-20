-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1199
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:30:52.851179+00:00
-- url     : https://prove2.me/submissions/78aa6500-4b72-459e-8348-2fe457c8ba16

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1200
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1201
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1202

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

lemma degreeUnionBranch62_1203 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 6 degreeUnionState62_1203 [6,9,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1204 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 7 degreeUnionState62_1204 [7,9,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1205 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 21 8 degreeUnionState62_1205 [8,9,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_1206 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 20 9 degreeUnionState62_1206 [9,9,11,13] = true := by
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

lemma degreeUnionBranch62_1199_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 9 degreeUnionState62_1199 [9,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1200
  · exact degreeUnionBranch62_1201
  · exact degreeUnionBranch62_1202
  · exact degreeUnionBranch62_1203
  · exact degreeUnionBranch62_1204
  · exact degreeUnionBranch62_1205
  · exact degreeUnionBranch62_1206

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1199_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1199_oai
