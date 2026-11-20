-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_131
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:29:39.926181+00:00
-- url     : https://prove2.me/submissions/9ec102b8-9b39-46c4-a117-059f57700c79

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_132
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_134
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_138
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_152
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_173
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_203
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_234

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

lemma degreeUnionBranch62_133 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 44 6 degreeUnionState62_133 [6,12] = true := by
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

lemma degreeUnionBranch62_131_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 50 12 degreeUnionState62_131 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_132
  · exact degreeUnionBranch62_133
  · exact degreeUnionBranch62_134
  · exact degreeUnionBranch62_138
  · exact degreeUnionBranch62_152
  · exact degreeUnionBranch62_173
  · exact degreeUnionBranch62_203
  · exact degreeUnionBranch62_234

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_131_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_131_oai
