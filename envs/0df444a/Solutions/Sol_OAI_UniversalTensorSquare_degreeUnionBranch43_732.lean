-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_732
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:54:59.436692+00:00
-- url     : https://prove2.me/submissions/ba47dae4-d5c4-4b0c-aeae-3bc17eb9e89c

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_733
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_734
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_735
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_736
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_737
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_739
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_740
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_741
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_742
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_743
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_744
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_745
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_746
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_747
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_748
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_749
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_750
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_751
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_752
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_753
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_754
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_755
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_756
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_757
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_758
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_759
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_760
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_761
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_762
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_763
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_764
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_765
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_766
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_767
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_768
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_769
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_770
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_771

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

lemma degreeUnionBranch43_738 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 34 9 degreeUnionState43_738 [9] = true := by
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

lemma degreeUnionBranch43_732_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 14*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_733
  · exact degreeUnionBranch43_734
  · exact degreeUnionBranch43_735
  · exact degreeUnionBranch43_736
  · exact degreeUnionBranch43_737
  · exact degreeUnionBranch43_738
  · exact degreeUnionBranch43_739
  · exact degreeUnionBranch43_740
  · exact degreeUnionBranch43_741
  · exact degreeUnionBranch43_742
  · exact degreeUnionBranch43_743
  · exact degreeUnionBranch43_744
  · exact degreeUnionBranch43_745
  · exact degreeUnionBranch43_746
  · exact degreeUnionBranch43_747
  · exact degreeUnionBranch43_748
  · exact degreeUnionBranch43_749
  · exact degreeUnionBranch43_750
  · exact degreeUnionBranch43_751
  · exact degreeUnionBranch43_752
  · exact degreeUnionBranch43_753
  · exact degreeUnionBranch43_754
  · exact degreeUnionBranch43_755
  · exact degreeUnionBranch43_756
  · exact degreeUnionBranch43_757
  · exact degreeUnionBranch43_758
  · exact degreeUnionBranch43_759
  · exact degreeUnionBranch43_760
  · exact degreeUnionBranch43_761
  · exact degreeUnionBranch43_762
  · exact degreeUnionBranch43_763
  · exact degreeUnionBranch43_764
  · exact degreeUnionBranch43_765
  · exact degreeUnionBranch43_766
  · exact degreeUnionBranch43_767
  · exact degreeUnionBranch43_768
  · exact degreeUnionBranch43_769
  · exact degreeUnionBranch43_770
  · exact degreeUnionBranch43_771

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_732_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_732_oai
