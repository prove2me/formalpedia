-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_57
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:41:15.831081+00:00
-- url     : https://prove2.me/submissions/1179915e-22c4-4f2f-a4af-22cfe28b04fd

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

lemma degreeUnionBranch35_58 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 23 4 degreeUnionState35_58 [4,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_59 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 22 5 degreeUnionState35_59 [5,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_60 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 21 6 degreeUnionState35_60 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_61 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 20 7 degreeUnionState35_61 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch35_62 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 19 8 degreeUnionState35_62 [8,8] = true := by
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

lemma degreeUnionBranch35_57_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 27 8 degreeUnionState35_57 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_58
  · exact degreeUnionBranch35_59
  · exact degreeUnionBranch35_60
  · exact degreeUnionBranch35_61
  · exact degreeUnionBranch35_62

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_57_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_57_oai
