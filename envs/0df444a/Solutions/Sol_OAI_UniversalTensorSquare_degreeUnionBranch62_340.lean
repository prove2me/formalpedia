-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_340
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:17:33.909216+00:00
-- url     : https://prove2.me/submissions/88ecd886-b6d3-4f90-97fc-91de20ecfa4f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

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

lemma degreeUnionBranch62_341 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 4 degreeUnionState62_341 [4,7,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_342 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 5 degreeUnionState62_342 [5,7,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_343 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 6 degreeUnionState62_343 [6,7,11,13] = true := by
  decide +kernel

lemma degreeUnionBranch62_344 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 7 degreeUnionState62_344 [7,7,11,13] = true := by
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

lemma degreeUnionBranch62_340_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 7 degreeUnionState62_340 [7,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_341
  · exact degreeUnionBranch62_342
  · exact degreeUnionBranch62_343
  · exact degreeUnionBranch62_344

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_340_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_340_oai
