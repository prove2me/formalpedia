-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_182
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:42:24.792311+00:00
-- url     : https://prove2.me/submissions/936850f7-0b47-4723-b874-4b96e4ad946f

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

lemma degreeUnionBranch62_183 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 4 degreeUnionState62_183 [4,8,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_184 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 5 degreeUnionState62_184 [5,8,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_185 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 6 degreeUnionState62_185 [6,8,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_186 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 7 degreeUnionState62_186 [7,8,10,12] = true := by
  decide +kernel

lemma degreeUnionBranch62_187 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 8 degreeUnionState62_187 [8,8,10,12] = true := by
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

lemma degreeUnionBranch62_182_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 8 degreeUnionState62_182 [8,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_183
  · exact degreeUnionBranch62_184
  · exact degreeUnionBranch62_185
  · exact degreeUnionBranch62_186
  · exact degreeUnionBranch62_187

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_182_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_182_oai
