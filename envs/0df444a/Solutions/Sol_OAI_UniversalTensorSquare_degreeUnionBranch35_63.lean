-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_63
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:41:21.855763+00:00
-- url     : https://prove2.me/submissions/aee8ee29-5386-45c9-98be-9777518040f7

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_64 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 22 4 degreeUnionState35_64 [4,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_65 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 21 5 degreeUnionState35_65 [5,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_66 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 20 6 degreeUnionState35_66 [6,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_67 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 19 7 degreeUnionState35_67 [7,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_68 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 18 8 degreeUnionState35_68 [8,9] = true := by
  decide +kernel

lemma degreeUnionBranch35_69 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 17 9 degreeUnionState35_69 [9,9] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_63_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 26 9 degreeUnionState35_63 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_64
  · exact degreeUnionBranch35_65
  · exact degreeUnionBranch35_66
  · exact degreeUnionBranch35_67
  · exact degreeUnionBranch35_68
  · exact degreeUnionBranch35_69

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_63_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_63_oai
