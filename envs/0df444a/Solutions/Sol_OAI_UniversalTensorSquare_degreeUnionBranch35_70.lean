-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_70
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:41:27.742785+00:00
-- url     : https://prove2.me/submissions/dc0b80dc-7eaf-4634-bde5-ccc5ec6b7674

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

lemma degreeUnionBranch35_71 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 21 4 degreeUnionState35_71 [4,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_72 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 20 5 degreeUnionState35_72 [5,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_73 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 19 6 degreeUnionState35_73 [6,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_74 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 18 7 degreeUnionState35_74 [7,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_75 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 17 8 degreeUnionState35_75 [8,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_76 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 16 9 degreeUnionState35_76 [9,10] = true := by
  decide +kernel

lemma degreeUnionBranch35_77 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 15 10 degreeUnionState35_77 [10,10] = true := by
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

lemma degreeUnionBranch35_70_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 25 10 degreeUnionState35_70 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_71
  · exact degreeUnionBranch35_72
  · exact degreeUnionBranch35_73
  · exact degreeUnionBranch35_74
  · exact degreeUnionBranch35_75
  · exact degreeUnionBranch35_76
  · exact degreeUnionBranch35_77

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_70_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_70_oai
