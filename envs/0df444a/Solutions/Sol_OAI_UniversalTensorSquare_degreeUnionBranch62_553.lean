-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_553
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:49:32.969381+00:00
-- url     : https://prove2.me/submissions/5b7fbb1d-eb91-43cd-8749-a2ae5185124a

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

lemma degreeUnionBranch62_554 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 4 degreeUnionState62_554 [4,10,10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_555 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 5 degreeUnionState62_555 [5,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_556 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 6 degreeUnionState62_556 [6,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_557 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 7 degreeUnionState62_557 [7,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_558 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 8 degreeUnionState62_558 [8,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_559 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 9 degreeUnionState62_559 [9,10,10,11] = true := by
  decide +kernel

lemma degreeUnionBranch62_560 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 10 degreeUnionState62_560 [10,10,10,11] = true := by
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

lemma degreeUnionBranch62_553_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 10 degreeUnionState62_553 [10,10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_554
  · exact degreeUnionBranch62_555
  · exact degreeUnionBranch62_556
  · exact degreeUnionBranch62_557
  · exact degreeUnionBranch62_558
  · exact degreeUnionBranch62_559
  · exact degreeUnionBranch62_560

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_553_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_553_oai
