-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:51:43.304202+00:00
-- url     : https://prove2.me/submissions/9b9b675e-3c14-4b9e-a282-2d7863899669

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_109
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_125
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_142
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_16
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_160
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_161
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_162
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_163
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_164
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_165
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_166
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_167
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_168
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_169
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_170
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_171
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_172
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_173
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_174
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_175
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_176
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_177
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_178
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_179
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_180
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_181
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_22
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_29
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_37
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_46
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_56
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_67
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_80
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_94

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

lemma degreeUnionBranch43_9 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 37 6 degreeUnionState43_9 [6] = true := by
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

lemma degreeUnionBranch43_8_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 8*a at hn
  have hlo : 6 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_9
  · exact degreeUnionBranch43_10
  · exact degreeUnionBranch43_11
  · exact degreeUnionBranch43_16
  · exact degreeUnionBranch43_22
  · exact degreeUnionBranch43_29
  · exact degreeUnionBranch43_37
  · exact degreeUnionBranch43_46
  · exact degreeUnionBranch43_56
  · exact degreeUnionBranch43_67
  · exact degreeUnionBranch43_80
  · exact degreeUnionBranch43_94
  · exact degreeUnionBranch43_109
  · exact degreeUnionBranch43_125
  · exact degreeUnionBranch43_142
  · exact degreeUnionBranch43_160
  · exact degreeUnionBranch43_161
  · exact degreeUnionBranch43_162
  · exact degreeUnionBranch43_163
  · exact degreeUnionBranch43_164
  · exact degreeUnionBranch43_165
  · exact degreeUnionBranch43_166
  · exact degreeUnionBranch43_167
  · exact degreeUnionBranch43_168
  · exact degreeUnionBranch43_169
  · exact degreeUnionBranch43_170
  · exact degreeUnionBranch43_171
  · exact degreeUnionBranch43_172
  · exact degreeUnionBranch43_173
  · exact degreeUnionBranch43_174
  · exact degreeUnionBranch43_175
  · exact degreeUnionBranch43_176
  · exact degreeUnionBranch43_177
  · exact degreeUnionBranch43_178
  · exact degreeUnionBranch43_179
  · exact degreeUnionBranch43_180
  · exact degreeUnionBranch43_181

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_8_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_8_oai
