-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_260
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:00:37.531123+00:00
-- url     : https://prove2.me/submissions/3f005e72-eae1-47c0-9440-3d77b832604a

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

lemma degreeUnionBranch39_261 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 24 3 degreeUnionState39_261 [3,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_262 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 23 4 degreeUnionState39_262 [4,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_263 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 22 5 degreeUnionState39_263 [5,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_264 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 21 6 degreeUnionState39_264 [6,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_265 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 20 7 degreeUnionState39_265 [7,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_266 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 19 8 degreeUnionState39_266 [8,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_267 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 18 9 degreeUnionState39_267 [9,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_268 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 17 10 degreeUnionState39_268 [10,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_269 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 16 11 degreeUnionState39_269 [11,12] = true := by
  decide +kernel

lemma degreeUnionBranch39_270 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 15 12 degreeUnionState39_270 [12,12] = true := by
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

lemma degreeUnionBranch39_260_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 27 12 degreeUnionState39_260 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 27 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_261
  · exact degreeUnionBranch39_262
  · exact degreeUnionBranch39_263
  · exact degreeUnionBranch39_264
  · exact degreeUnionBranch39_265
  · exact degreeUnionBranch39_266
  · exact degreeUnionBranch39_267
  · exact degreeUnionBranch39_268
  · exact degreeUnionBranch39_269
  · exact degreeUnionBranch39_270

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_260_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_260_oai
