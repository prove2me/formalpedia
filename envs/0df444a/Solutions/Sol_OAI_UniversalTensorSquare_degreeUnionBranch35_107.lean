-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_107
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:32:36.548502+00:00
-- url     : https://prove2.me/submissions/6804fb72-b484-407d-8e56-41c0304f10d3

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

lemma degreeUnionBranch35_108 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 24 3 degreeUnionState35_108 [3,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_109 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 23 4 degreeUnionState35_109 [4,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_110 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 22 5 degreeUnionState35_110 [5,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_111 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 21 6 degreeUnionState35_111 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_112 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 20 7 degreeUnionState35_112 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_113 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 19 8 degreeUnionState35_113 [8,8] = true := by
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

lemma degreeUnionBranch35_107_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 27 8 degreeUnionState35_107 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 27 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_108
  · exact degreeUnionBranch35_109
  · exact degreeUnionBranch35_110
  · exact degreeUnionBranch35_111
  · exact degreeUnionBranch35_112
  · exact degreeUnionBranch35_113

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_107_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_107_oai
