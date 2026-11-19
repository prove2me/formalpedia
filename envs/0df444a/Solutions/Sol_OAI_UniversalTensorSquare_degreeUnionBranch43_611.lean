-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_611
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:26:25.485047+00:00
-- url     : https://prove2.me/submissions/6ab24c70-4789-4104-bd9c-fe5cc4d3fa44

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_612
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_613
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_614
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_615
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_617
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_624
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_633
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_643
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_654
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_655
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_656
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_657
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_658
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_659
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_660
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_661
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_662
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_663
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_664
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_665
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_666
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_667
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_668
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_669
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_670
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_671
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_672
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_673
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_674
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_675
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_676
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_677
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_678
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_679
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_680
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_681
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_682
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_683

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

lemma degreeUnionBranch43_616 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 35 8 degreeUnionState43_616 [8] = true := by
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

lemma degreeUnionBranch43_611_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_612
  · exact degreeUnionBranch43_613
  · exact degreeUnionBranch43_614
  · exact degreeUnionBranch43_615
  · exact degreeUnionBranch43_616
  · exact degreeUnionBranch43_617
  · exact degreeUnionBranch43_624
  · exact degreeUnionBranch43_633
  · exact degreeUnionBranch43_643
  · exact degreeUnionBranch43_654
  · exact degreeUnionBranch43_655
  · exact degreeUnionBranch43_656
  · exact degreeUnionBranch43_657
  · exact degreeUnionBranch43_658
  · exact degreeUnionBranch43_659
  · exact degreeUnionBranch43_660
  · exact degreeUnionBranch43_661
  · exact degreeUnionBranch43_662
  · exact degreeUnionBranch43_663
  · exact degreeUnionBranch43_664
  · exact degreeUnionBranch43_665
  · exact degreeUnionBranch43_666
  · exact degreeUnionBranch43_667
  · exact degreeUnionBranch43_668
  · exact degreeUnionBranch43_669
  · exact degreeUnionBranch43_670
  · exact degreeUnionBranch43_671
  · exact degreeUnionBranch43_672
  · exact degreeUnionBranch43_673
  · exact degreeUnionBranch43_674
  · exact degreeUnionBranch43_675
  · exact degreeUnionBranch43_676
  · exact degreeUnionBranch43_677
  · exact degreeUnionBranch43_678
  · exact degreeUnionBranch43_679
  · exact degreeUnionBranch43_680
  · exact degreeUnionBranch43_681
  · exact degreeUnionBranch43_682
  · exact degreeUnionBranch43_683

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_611_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_611_oai
