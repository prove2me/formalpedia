-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_680
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:54:13.932702+00:00
-- url     : https://prove2.me/submissions/5520d21e-ed71-4b8a-af19-f5f2e6f18187

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_681
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_682
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_684
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_689
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_696
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_704
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_705
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_706

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

lemma degreeUnionBranch62_683 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 6 degreeUnionState62_683 [6,12,12] = true := by
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

lemma degreeUnionBranch62_680_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 38 12 degreeUnionState62_680 [12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 38 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_681
  · exact degreeUnionBranch62_682
  · exact degreeUnionBranch62_683
  · exact degreeUnionBranch62_684
  · exact degreeUnionBranch62_689
  · exact degreeUnionBranch62_696
  · exact degreeUnionBranch62_704
  · exact degreeUnionBranch62_705
  · exact degreeUnionBranch62_706

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_680_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_680_oai
