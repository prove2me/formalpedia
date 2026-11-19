-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_121
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:41.256696+00:00
-- url     : https://prove2.me/submissions/4ba84eb9-17e3-4fa3-9051-86f50e01d4aa

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_122
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_123
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_125
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_131
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_138
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_146
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_155
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_165
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_176
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_188
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_202
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_203
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_204
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_205
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_206
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_207
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_208
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_209
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_210
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_211
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_212
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_213
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_214
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_215
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_216
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_217
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_218
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_219
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_220
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_221
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_222
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_223
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch39_224

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

lemma degreeUnionBranch39_124 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 32 7 degreeUnionState39_124 [7] = true := by
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

lemma degreeUnionBranch39_121_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 39 38 degreeHalfRegions39 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 38 at hb
  change 39 ≤ 9*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_122
  · exact degreeUnionBranch39_123
  · exact degreeUnionBranch39_124
  · exact degreeUnionBranch39_125
  · exact degreeUnionBranch39_131
  · exact degreeUnionBranch39_138
  · exact degreeUnionBranch39_146
  · exact degreeUnionBranch39_155
  · exact degreeUnionBranch39_165
  · exact degreeUnionBranch39_176
  · exact degreeUnionBranch39_188
  · exact degreeUnionBranch39_202
  · exact degreeUnionBranch39_203
  · exact degreeUnionBranch39_204
  · exact degreeUnionBranch39_205
  · exact degreeUnionBranch39_206
  · exact degreeUnionBranch39_207
  · exact degreeUnionBranch39_208
  · exact degreeUnionBranch39_209
  · exact degreeUnionBranch39_210
  · exact degreeUnionBranch39_211
  · exact degreeUnionBranch39_212
  · exact degreeUnionBranch39_213
  · exact degreeUnionBranch39_214
  · exact degreeUnionBranch39_215
  · exact degreeUnionBranch39_216
  · exact degreeUnionBranch39_217
  · exact degreeUnionBranch39_218
  · exact degreeUnionBranch39_219
  · exact degreeUnionBranch39_220
  · exact degreeUnionBranch39_221
  · exact degreeUnionBranch39_222
  · exact degreeUnionBranch39_223
  · exact degreeUnionBranch39_224

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_121_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_121_oai
