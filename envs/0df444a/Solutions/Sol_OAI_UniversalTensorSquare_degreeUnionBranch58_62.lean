-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_62
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:50:49.168073+00:00
-- url     : https://prove2.me/submissions/8a0e8903-1011-42b4-af39-4f46b8bb8410

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_63
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_64
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_65
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_68
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_69
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_70
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_80
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch58_91

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_66 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 50 8 degreeUnionState58_66 [8] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_67 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 49 9 degreeUnionState58_67 [9] = true := by
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_62_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 58 14 degreeHalfRegions58 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 58 ≤ 13*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_63
  · exact degreeUnionBranch58_64
  · exact degreeUnionBranch58_65
  · exact degreeUnionBranch58_66
  · exact degreeUnionBranch58_67
  · exact degreeUnionBranch58_68
  · exact degreeUnionBranch58_69
  · exact degreeUnionBranch58_70
  · exact degreeUnionBranch58_80
  · exact degreeUnionBranch58_91

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_62_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_62_oai
