-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1279
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:02:56.39727+00:00
-- url     : https://prove2.me/submissions/f0cb6adf-c05c-4321-b49a-73fcfd9f35a9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1280

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

lemma degreeUnionBranch62_1281 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 4 degreeUnionState62_1281 [4,8,10,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_1282 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 5 degreeUnionState62_1282 [5,8,10,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_1283 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 6 degreeUnionState62_1283 [6,8,10,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_1284 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 7 degreeUnionState62_1284 [7,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_1285 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 8 degreeUnionState62_1285 [8,8,10,14] = true := by
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

lemma degreeUnionBranch62_1279_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 8 degreeUnionState62_1279 [8,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1280
  · exact degreeUnionBranch62_1281
  · exact degreeUnionBranch62_1282
  · exact degreeUnionBranch62_1283
  · exact degreeUnionBranch62_1284
  · exact degreeUnionBranch62_1285

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1279_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1279_oai
