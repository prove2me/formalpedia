-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_67
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:31:34.623934+00:00
-- url     : https://prove2.me/submissions/45b133d7-bcb4-4807-9a30-e70668950a28

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_68
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_69
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_70
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_71
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_72
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_73
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_74
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_75
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_76
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_77
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_78
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch43_79

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

lemma degreeUnionBranch43_67_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 28 15 degreeUnionState43_67 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 15 at hb
  change 28 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_68
  · exact degreeUnionBranch43_69
  · exact degreeUnionBranch43_70
  · exact degreeUnionBranch43_71
  · exact degreeUnionBranch43_72
  · exact degreeUnionBranch43_73
  · exact degreeUnionBranch43_74
  · exact degreeUnionBranch43_75
  · exact degreeUnionBranch43_76
  · exact degreeUnionBranch43_77
  · exact degreeUnionBranch43_78
  · exact degreeUnionBranch43_79

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_67_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_67_oai
