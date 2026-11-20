-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1242
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:47:02.335229+00:00
-- url     : https://prove2.me/submissions/1c9baa23-5b86-447a-b2a5-bfd8c40a8bcd

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1243
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1247

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

lemma degreeUnionBranch62_1244 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 35 5 degreeUnionState62_1244 [5,8,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_1245 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 6 degreeUnionState62_1245 [6,8,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_1246 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 7 degreeUnionState62_1246 [7,8,14] = true := by
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

lemma degreeUnionBranch62_1242_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 8 degreeUnionState62_1242 [8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 40 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1243
  · exact degreeUnionBranch62_1244
  · exact degreeUnionBranch62_1245
  · exact degreeUnionBranch62_1246
  · exact degreeUnionBranch62_1247

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1242_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1242_oai
