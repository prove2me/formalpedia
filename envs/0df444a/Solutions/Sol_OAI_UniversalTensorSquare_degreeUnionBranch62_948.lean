-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_948
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:06:08.030592+00:00
-- url     : https://prove2.me/submissions/d87f480b-f1cb-4b9c-93ef-e96819df4f33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1003
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1121
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1237
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_954
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_962

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_949 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 57 5 degreeUnionState62_949 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_950 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 56 6 degreeUnionState62_950 [6] = true := by
  decide +kernel

lemma degreeUnionBranch62_951 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 55 7 degreeUnionState62_951 [7] = true := by
  decide +kernel

lemma degreeUnionBranch62_952 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 54 8 degreeUnionState62_952 [8] = true := by
  decide +kernel

lemma degreeUnionBranch62_953 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 53 9 degreeUnionState62_953 [9] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_1323 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 47 15 degreeUnionState62_1323 [15] = true := by
  decide +kernel

lemma degreeUnionBranch62_1324 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 46 16 degreeUnionState62_1324 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_1325 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 45 17 degreeUnionState62_1325 [17] = true := by
  decide +kernel

lemma degreeUnionBranch62_1326 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 44 18 degreeUnionState62_1326 [18] = true := by
  decide +kernel

lemma degreeUnionBranch62_1327 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 43 19 degreeUnionState62_1327 [19] = true := by
  decide +kernel

lemma degreeUnionBranch62_1328 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 42 20 degreeUnionState62_1328 [20] = true := by
  decide +kernel

lemma degreeUnionBranch62_1329 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 41 21 degreeUnionState62_1329 [21] = true := by
  decide +kernel

lemma degreeUnionBranch62_1330 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 40 22 degreeUnionState62_1330 [22] = true := by
  decide +kernel

lemma degreeUnionBranch62_1331 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 39 23 degreeUnionState62_1331 [23] = true := by
  decide +kernel

lemma degreeUnionBranch62_1332 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 38 24 degreeUnionState62_1332 [24] = true := by
  decide +kernel

lemma degreeUnionBranch62_1333 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 37 25 degreeUnionState62_1333 [25] = true := by
  decide +kernel

lemma degreeUnionBranch62_1334 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 36 26 degreeUnionState62_1334 [26] = true := by
  decide +kernel

lemma degreeUnionBranch62_1335 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 35 27 degreeUnionState62_1335 [27] = true := by
  decide +kernel

lemma degreeUnionBranch62_1336 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 34 28 degreeUnionState62_1336 [28] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_948_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 14 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 14*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_949
  · exact degreeUnionBranch62_950
  · exact degreeUnionBranch62_951
  · exact degreeUnionBranch62_952
  · exact degreeUnionBranch62_953
  · exact degreeUnionBranch62_954
  · exact degreeUnionBranch62_962
  · exact degreeUnionBranch62_1003
  · exact degreeUnionBranch62_1121
  · exact degreeUnionBranch62_1237
  · exact degreeUnionBranch62_1323
  · exact degreeUnionBranch62_1324
  · exact degreeUnionBranch62_1325
  · exact degreeUnionBranch62_1326
  · exact degreeUnionBranch62_1327
  · exact degreeUnionBranch62_1328
  · exact degreeUnionBranch62_1329
  · exact degreeUnionBranch62_1330
  · exact degreeUnionBranch62_1331
  · exact degreeUnionBranch62_1332
  · exact degreeUnionBranch62_1333
  · exact degreeUnionBranch62_1334
  · exact degreeUnionBranch62_1335
  · exact degreeUnionBranch62_1336

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_948_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_948_oai
