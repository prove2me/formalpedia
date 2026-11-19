-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_684
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:38:55.055814+00:00
-- url     : https://prove2.me/submissions/60ca44f3-0650-44a8-8ef3-6d1722ddb3df

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_685
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_686
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_687
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_688
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_689
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_691
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_700
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_701
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_702
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_703
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_704
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_705
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_706
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_707
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_708
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_709
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_710
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_711
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_712
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_713
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_714
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_715
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_716
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_717
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_718
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_719
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_720
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_721
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_722
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_723
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_724
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_725
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_726
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_727
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_728
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_729
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_730
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_731

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

lemma degreeUnionBranch43_690 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 34 9 degreeUnionState43_690 [9] = true := by
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

lemma degreeUnionBranch43_684_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_685
  · exact degreeUnionBranch43_686
  · exact degreeUnionBranch43_687
  · exact degreeUnionBranch43_688
  · exact degreeUnionBranch43_689
  · exact degreeUnionBranch43_690
  · exact degreeUnionBranch43_691
  · exact degreeUnionBranch43_700
  · exact degreeUnionBranch43_701
  · exact degreeUnionBranch43_702
  · exact degreeUnionBranch43_703
  · exact degreeUnionBranch43_704
  · exact degreeUnionBranch43_705
  · exact degreeUnionBranch43_706
  · exact degreeUnionBranch43_707
  · exact degreeUnionBranch43_708
  · exact degreeUnionBranch43_709
  · exact degreeUnionBranch43_710
  · exact degreeUnionBranch43_711
  · exact degreeUnionBranch43_712
  · exact degreeUnionBranch43_713
  · exact degreeUnionBranch43_714
  · exact degreeUnionBranch43_715
  · exact degreeUnionBranch43_716
  · exact degreeUnionBranch43_717
  · exact degreeUnionBranch43_718
  · exact degreeUnionBranch43_719
  · exact degreeUnionBranch43_720
  · exact degreeUnionBranch43_721
  · exact degreeUnionBranch43_722
  · exact degreeUnionBranch43_723
  · exact degreeUnionBranch43_724
  · exact degreeUnionBranch43_725
  · exact degreeUnionBranch43_726
  · exact degreeUnionBranch43_727
  · exact degreeUnionBranch43_728
  · exact degreeUnionBranch43_729
  · exact degreeUnionBranch43_730
  · exact degreeUnionBranch43_731

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_684_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_684_oai
