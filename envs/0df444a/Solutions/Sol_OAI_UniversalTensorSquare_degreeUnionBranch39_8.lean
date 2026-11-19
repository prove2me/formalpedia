-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:10:21.351297+00:00
-- url     : https://prove2.me/submissions/7af37386-d6a0-4eb0-9b82-d14433f4c2d0

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_100
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_101
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_102
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_103
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_104
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_105
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_106
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_107
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_108
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_109
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_110
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_111
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_112
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_113
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_114
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_115
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_116
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_117
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_118
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_119
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_12
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_120
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_17
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_23
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_30
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_39
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_49
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_60
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_72
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_85
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_99

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

lemma degreeUnionBranch39_9 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 34 5 degreeUnionState39_9 [5] = true := by
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

lemma degreeUnionBranch39_8_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 39 38 degreeHalfRegions39 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 38 at hb
  change 39 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_9
  · exact degreeUnionBranch39_10
  · exact degreeUnionBranch39_11
  · exact degreeUnionBranch39_12
  · exact degreeUnionBranch39_17
  · exact degreeUnionBranch39_23
  · exact degreeUnionBranch39_30
  · exact degreeUnionBranch39_39
  · exact degreeUnionBranch39_49
  · exact degreeUnionBranch39_60
  · exact degreeUnionBranch39_72
  · exact degreeUnionBranch39_85
  · exact degreeUnionBranch39_99
  · exact degreeUnionBranch39_100
  · exact degreeUnionBranch39_101
  · exact degreeUnionBranch39_102
  · exact degreeUnionBranch39_103
  · exact degreeUnionBranch39_104
  · exact degreeUnionBranch39_105
  · exact degreeUnionBranch39_106
  · exact degreeUnionBranch39_107
  · exact degreeUnionBranch39_108
  · exact degreeUnionBranch39_109
  · exact degreeUnionBranch39_110
  · exact degreeUnionBranch39_111
  · exact degreeUnionBranch39_112
  · exact degreeUnionBranch39_113
  · exact degreeUnionBranch39_114
  · exact degreeUnionBranch39_115
  · exact degreeUnionBranch39_116
  · exact degreeUnionBranch39_117
  · exact degreeUnionBranch39_118
  · exact degreeUnionBranch39_119
  · exact degreeUnionBranch39_120

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_8_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_8_oai
