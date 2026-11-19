-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:36:02.547225+00:00
-- url     : https://prove2.me/submissions/b2839f32-f5ed-490e-a03a-ca1109dcc4a8

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

lemma degreeUnionBranch35_21 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 21 4 degreeUnionState35_21 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_22 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 20 5 degreeUnionState35_22 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_23 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 19 6 degreeUnionState35_23 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_24 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 18 7 degreeUnionState35_24 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_25 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 17 8 degreeUnionState35_25 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_26 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 16 9 degreeUnionState35_26 [9,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_27 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 6 15 10 degreeUnionState35_27 [10,10] = true := by
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

lemma degreeUnionBranch35_20_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 25 10 degreeUnionState35_20 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_21
  · exact degreeUnionBranch35_22
  · exact degreeUnionBranch35_23
  · exact degreeUnionBranch35_24
  · exact degreeUnionBranch35_25
  · exact degreeUnionBranch35_26
  · exact degreeUnionBranch35_27

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_20_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_20_oai
