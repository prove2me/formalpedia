-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:29.289725+00:00
-- url     : https://prove2.me/submissions/03cacee5-152f-4544-978c-7eac9b8688ff

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

lemma degreeUnionBranch39_13 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 26 5 degreeUnionState39_13 [5,8] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_14 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 25 6 degreeUnionState39_14 [6,8] = true := by
  decide +kernel

lemma degreeUnionBranch39_15 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 24 7 degreeUnionState39_15 [7,8] = true := by
  decide +kernel

lemma degreeUnionBranch39_16 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 6 23 8 degreeUnionState39_16 [8,8] = true := by
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

lemma degreeUnionBranch39_12_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 31 8 degreeUnionState39_12 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_13
  · exact degreeUnionBranch39_14
  · exact degreeUnionBranch39_15
  · exact degreeUnionBranch39_16

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_12_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_12_oai
