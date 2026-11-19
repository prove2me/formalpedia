-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:09:57.590072+00:00
-- url     : https://prove2.me/submissions/39cb6336-4dba-488b-b438-0a949b6023ff

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_40 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 23 4 degreeUnionState39_40 [4,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_41 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 22 5 degreeUnionState39_41 [5,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_42 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 21 6 degreeUnionState39_42 [6,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_43 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 20 7 degreeUnionState39_43 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_44 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 19 8 degreeUnionState39_44 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_45 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 18 9 degreeUnionState39_45 [9,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_46 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 17 10 degreeUnionState39_46 [10,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_47 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 16 11 degreeUnionState39_47 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_48 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 15 12 degreeUnionState39_48 [12,12] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_39_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 27 12 degreeUnionState39_39 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 27 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_40
  · exact degreeUnionBranch39_41
  · exact degreeUnionBranch39_42
  · exact degreeUnionBranch39_43
  · exact degreeUnionBranch39_44
  · exact degreeUnionBranch39_45
  · exact degreeUnionBranch39_46
  · exact degreeUnionBranch39_47
  · exact degreeUnionBranch39_48

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_39_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_39_oai
