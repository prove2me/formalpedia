-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_624
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:27:04.526725+00:00
-- url     : https://prove2.me/submissions/79013c98-60f7-4557-803d-2cb6f033a43a

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_625 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 30 3 degreeUnionState43_625 [3,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_626 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 29 4 degreeUnionState43_626 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_627 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 28 5 degreeUnionState43_627 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_628 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 27 6 degreeUnionState43_628 [6,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_629 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 26 7 degreeUnionState43_629 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_630 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 25 8 degreeUnionState43_630 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_631 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 24 9 degreeUnionState43_631 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch43_632 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 23 10 degreeUnionState43_632 [10,10] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_624_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 33 10 degreeUnionState43_624 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_625
  · exact degreeUnionBranch43_626
  · exact degreeUnionBranch43_627
  · exact degreeUnionBranch43_628
  · exact degreeUnionBranch43_629
  · exact degreeUnionBranch43_630
  · exact degreeUnionBranch43_631
  · exact degreeUnionBranch43_632

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_624_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_624_oai
