-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_294
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:43:42.761268+00:00
-- url     : https://prove2.me/submissions/9d295605-5f0d-4c45-bd5e-2f4fa69740ab

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

lemma degreeUnionBranch43_295 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 21 4 degreeUnionState43_295 [4,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_296 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 5 degreeUnionState43_296 [5,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_297 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 6 degreeUnionState43_297 [6,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_298 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 18 7 degreeUnionState43_298 [7,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_299 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 8 degreeUnionState43_299 [8,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_300 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 16 9 degreeUnionState43_300 [9,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_301 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 15 10 degreeUnionState43_301 [10,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_302 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 14 11 degreeUnionState43_302 [11,18] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_303 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 13 12 degreeUnionState43_303 [12,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_304 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 12 13 degreeUnionState43_304 [13,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_305 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 11 14 degreeUnionState43_305 [14,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_306 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 10 15 degreeUnionState43_306 [15,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_307 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 9 16 degreeUnionState43_307 [16,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_308 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 8 17 degreeUnionState43_308 [17,18] = true := by
  decide +kernel

lemma degreeUnionBranch43_309 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 7 18 degreeUnionState43_309 [18,18] = true := by
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

lemma degreeUnionBranch43_294_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 18 degreeUnionState43_294 [18] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 18 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_295
  · exact degreeUnionBranch43_296
  · exact degreeUnionBranch43_297
  · exact degreeUnionBranch43_298
  · exact degreeUnionBranch43_299
  · exact degreeUnionBranch43_300
  · exact degreeUnionBranch43_301
  · exact degreeUnionBranch43_302
  · exact degreeUnionBranch43_303
  · exact degreeUnionBranch43_304
  · exact degreeUnionBranch43_305
  · exact degreeUnionBranch43_306
  · exact degreeUnionBranch43_307
  · exact degreeUnionBranch43_308
  · exact degreeUnionBranch43_309

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_294_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_294_oai
