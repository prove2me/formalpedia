-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch58_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:42:12.551777+00:00
-- url     : https://prove2.me/submissions/bb7ead7a-8c1f-4c44-aa8e-5b3d62cf89ae

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_25

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_21 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 41 5 degreeUnionState58_21 [5,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_22 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 40 6 degreeUnionState58_22 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_23 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 39 7 degreeUnionState58_23 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_24 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 38 8 degreeUnionState58_24 [8,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_32 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 36 10 degreeUnionState58_32 [10,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_33 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 35 11 degreeUnionState58_33 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch58_34 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 34 12 degreeUnionState58_34 [12,12] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_20_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 46 12 degreeUnionState58_20 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 46 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_21
  · exact degreeUnionBranch58_22
  · exact degreeUnionBranch58_23
  · exact degreeUnionBranch58_24
  · exact degreeUnionBranch58_25
  · exact degreeUnionBranch58_32
  · exact degreeUnionBranch58_33
  · exact degreeUnionBranch58_34

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_20_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_20_oai
