-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_351
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:49:19.293701+00:00
-- url     : https://prove2.me/submissions/edcfccb1-3e28-4e85-9c5a-31288effbd9e

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_352
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_353
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_355
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_366
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_384
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_392
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_401
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_411
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_422
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_434
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_447
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_462
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_478
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_495
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_513
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_514
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_515
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_516
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_517
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_518
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_519
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_520
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_521
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_522
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_523
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_524
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_525
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_526
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_527
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_528
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_529
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_530
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_531
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_532
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_533
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_534
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_535

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

lemma degreeUnionBranch43_354 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 36 7 degreeUnionState43_354 [7] = true := by
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

lemma degreeUnionBranch43_351_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_352
  · exact degreeUnionBranch43_353
  · exact degreeUnionBranch43_354
  · exact degreeUnionBranch43_355
  · exact degreeUnionBranch43_366
  · exact degreeUnionBranch43_384
  · exact degreeUnionBranch43_392
  · exact degreeUnionBranch43_401
  · exact degreeUnionBranch43_411
  · exact degreeUnionBranch43_422
  · exact degreeUnionBranch43_434
  · exact degreeUnionBranch43_447
  · exact degreeUnionBranch43_462
  · exact degreeUnionBranch43_478
  · exact degreeUnionBranch43_495
  · exact degreeUnionBranch43_513
  · exact degreeUnionBranch43_514
  · exact degreeUnionBranch43_515
  · exact degreeUnionBranch43_516
  · exact degreeUnionBranch43_517
  · exact degreeUnionBranch43_518
  · exact degreeUnionBranch43_519
  · exact degreeUnionBranch43_520
  · exact degreeUnionBranch43_521
  · exact degreeUnionBranch43_522
  · exact degreeUnionBranch43_523
  · exact degreeUnionBranch43_524
  · exact degreeUnionBranch43_525
  · exact degreeUnionBranch43_526
  · exact degreeUnionBranch43_527
  · exact degreeUnionBranch43_528
  · exact degreeUnionBranch43_529
  · exact degreeUnionBranch43_530
  · exact degreeUnionBranch43_531
  · exact degreeUnionBranch43_532
  · exact degreeUnionBranch43_533
  · exact degreeUnionBranch43_534
  · exact degreeUnionBranch43_535

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_351_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_351_oai
