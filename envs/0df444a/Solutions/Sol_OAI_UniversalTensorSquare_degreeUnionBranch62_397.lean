-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_397
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:47:40.612888+00:00
-- url     : https://prove2.me/submissions/b5955c9d-f9e3-4d08-8293-eaeef8df35f5

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_400

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

lemma degreeUnionBranch62_398 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 36 5 degreeUnionState62_398 [5,7,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_399 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 6 degreeUnionState62_399 [6,7,14] = true := by
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

lemma degreeUnionBranch62_397_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 41 7 degreeUnionState62_397 [7,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 7 at hb
  change 41 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_398
  · exact degreeUnionBranch62_399
  · exact degreeUnionBranch62_400

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_397_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_397_oai
