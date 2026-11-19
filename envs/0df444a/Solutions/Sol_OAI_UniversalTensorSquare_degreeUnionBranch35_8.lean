-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch35_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:41:33.562506+00:00
-- url     : https://prove2.me/submissions/0cc37375-c6eb-4abd-a7d1-0a870dbe1e26

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_10
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_11
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_12
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_13
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_20
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_28
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_29
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_30
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_31
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_32
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_33
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_34
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_35
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_36
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_37
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_38
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_39
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_40
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_41
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_42
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_43
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_44
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_45
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_46
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_47
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_48
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_49
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_50
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_51
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch35_9

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_8_oai : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 35 34 degreeHalfRegions35 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 34 at hb
  change 35 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_9
  · exact degreeUnionBranch35_10
  · exact degreeUnionBranch35_11
  · exact degreeUnionBranch35_12
  · exact degreeUnionBranch35_13
  · exact degreeUnionBranch35_20
  · exact degreeUnionBranch35_28
  · exact degreeUnionBranch35_29
  · exact degreeUnionBranch35_30
  · exact degreeUnionBranch35_31
  · exact degreeUnionBranch35_32
  · exact degreeUnionBranch35_33
  · exact degreeUnionBranch35_34
  · exact degreeUnionBranch35_35
  · exact degreeUnionBranch35_36
  · exact degreeUnionBranch35_37
  · exact degreeUnionBranch35_38
  · exact degreeUnionBranch35_39
  · exact degreeUnionBranch35_40
  · exact degreeUnionBranch35_41
  · exact degreeUnionBranch35_42
  · exact degreeUnionBranch35_43
  · exact degreeUnionBranch35_44
  · exact degreeUnionBranch35_45
  · exact degreeUnionBranch35_46
  · exact degreeUnionBranch35_47
  · exact degreeUnionBranch35_48
  · exact degreeUnionBranch35_49
  · exact degreeUnionBranch35_50
  · exact degreeUnionBranch35_51

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch35_8_oai := @OAI.UniversalTensorSquare.degreeUnionBranch35_8_oai
