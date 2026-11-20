-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_838
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:50:41.529141+00:00
-- url     : https://prove2.me/submissions/0b64d451-dc86-425a-8de0-02f5fe3085e1

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_839

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

lemma degreeUnionBranch62_840 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 5 degreeUnionState62_840 [5,7,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_841 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 6 degreeUnionState62_841 [6,7,14] = true := by
  decide +kernel

lemma degreeUnionBranch62_842 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 7 degreeUnionState62_842 [7,7,14] = true := by
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

lemma degreeUnionBranch62_838_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 7 degreeUnionState62_838 [7,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 41 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_839
  · exact degreeUnionBranch62_840
  · exact degreeUnionBranch62_841
  · exact degreeUnionBranch62_842

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_838_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_838_oai
