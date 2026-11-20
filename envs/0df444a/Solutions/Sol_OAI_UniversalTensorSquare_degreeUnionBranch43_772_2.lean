-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_772
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:37:04.87547+00:00
-- url     : https://prove2.me/submissions/607440f4-2f29-40a0-83d4-bb6f05413cf9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_773
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_774
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_775
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_776
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_777
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_780
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_781
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_782
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_783
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_784
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_785
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_786
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_787
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_788
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_789
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_790
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_791
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_792
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_793
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_794
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_795
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_796
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_797
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_798
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_799
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_800
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_801
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_802
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_803
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_804
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_805
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_806
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_807
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_808
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_809
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_810
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_811
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_812

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

lemma degreeUnionBranch43_778 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 35 8 degreeUnionState43_778 [8] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_779 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 34 9 degreeUnionState43_779 [9] = true := by
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

lemma degreeUnionBranch43_772_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 15*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_773
  · exact degreeUnionBranch43_774
  · exact degreeUnionBranch43_775
  · exact degreeUnionBranch43_776
  · exact degreeUnionBranch43_777
  · exact degreeUnionBranch43_778
  · exact degreeUnionBranch43_779
  · exact degreeUnionBranch43_780
  · exact degreeUnionBranch43_781
  · exact degreeUnionBranch43_782
  · exact degreeUnionBranch43_783
  · exact degreeUnionBranch43_784
  · exact degreeUnionBranch43_785
  · exact degreeUnionBranch43_786
  · exact degreeUnionBranch43_787
  · exact degreeUnionBranch43_788
  · exact degreeUnionBranch43_789
  · exact degreeUnionBranch43_790
  · exact degreeUnionBranch43_791
  · exact degreeUnionBranch43_792
  · exact degreeUnionBranch43_793
  · exact degreeUnionBranch43_794
  · exact degreeUnionBranch43_795
  · exact degreeUnionBranch43_796
  · exact degreeUnionBranch43_797
  · exact degreeUnionBranch43_798
  · exact degreeUnionBranch43_799
  · exact degreeUnionBranch43_800
  · exact degreeUnionBranch43_801
  · exact degreeUnionBranch43_802
  · exact degreeUnionBranch43_803
  · exact degreeUnionBranch43_804
  · exact degreeUnionBranch43_805
  · exact degreeUnionBranch43_806
  · exact degreeUnionBranch43_807
  · exact degreeUnionBranch43_808
  · exact degreeUnionBranch43_809
  · exact degreeUnionBranch43_810
  · exact degreeUnionBranch43_811
  · exact degreeUnionBranch43_812

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_772_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_772_oai
