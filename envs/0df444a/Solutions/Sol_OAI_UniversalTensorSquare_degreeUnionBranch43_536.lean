-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_536
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:20:04.840211+00:00
-- url     : https://prove2.me/submissions/baa7cbe2-70df-4a54-b3d4-3f4855480603

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_537
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_538
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_539
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_541
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_547
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_554
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_562
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_571
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_581
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_582
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_583
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_584
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_585
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_586
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_587
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_588
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_589
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_590
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_591
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_592
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_593
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_594
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_595
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_596
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_597
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_598
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_599
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_600
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_601
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_602
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_603
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_604
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_605
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_606
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_607
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_608
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_609
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_610

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

lemma degreeUnionBranch43_540 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 36 7 degreeUnionState43_540 [7] = true := by
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

lemma degreeUnionBranch43_536_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_537
  · exact degreeUnionBranch43_538
  · exact degreeUnionBranch43_539
  · exact degreeUnionBranch43_540
  · exact degreeUnionBranch43_541
  · exact degreeUnionBranch43_547
  · exact degreeUnionBranch43_554
  · exact degreeUnionBranch43_562
  · exact degreeUnionBranch43_571
  · exact degreeUnionBranch43_581
  · exact degreeUnionBranch43_582
  · exact degreeUnionBranch43_583
  · exact degreeUnionBranch43_584
  · exact degreeUnionBranch43_585
  · exact degreeUnionBranch43_586
  · exact degreeUnionBranch43_587
  · exact degreeUnionBranch43_588
  · exact degreeUnionBranch43_589
  · exact degreeUnionBranch43_590
  · exact degreeUnionBranch43_591
  · exact degreeUnionBranch43_592
  · exact degreeUnionBranch43_593
  · exact degreeUnionBranch43_594
  · exact degreeUnionBranch43_595
  · exact degreeUnionBranch43_596
  · exact degreeUnionBranch43_597
  · exact degreeUnionBranch43_598
  · exact degreeUnionBranch43_599
  · exact degreeUnionBranch43_600
  · exact degreeUnionBranch43_601
  · exact degreeUnionBranch43_602
  · exact degreeUnionBranch43_603
  · exact degreeUnionBranch43_604
  · exact degreeUnionBranch43_605
  · exact degreeUnionBranch43_606
  · exact degreeUnionBranch43_607
  · exact degreeUnionBranch43_608
  · exact degreeUnionBranch43_609
  · exact degreeUnionBranch43_610

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_536_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_536_oai
