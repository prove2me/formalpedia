-- Prove2me | solution 1 for OAI.UniversalTensorSquare.universal_partition_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:07:21.381769+00:00
-- url     : https://prove2.me/submissions/dd16f115-7756-4e12-a2c3-95b095d8f044

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_cone
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_semantic_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck116
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTreeAll116
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos112
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos118
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos151
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos89
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos106
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos108
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos110
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos114
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos149
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos71
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos73
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos75
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos77
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos79
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos81
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos83
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos85
import Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos87
import Theorems.Thm_OAI_UniversalTensorSquare_treeResidual_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCone116_1 (μ : YoungDiagram) (hμ : μ.card = 116)
    (hd : RowsDom μ.rowLens degreeRows116_1) : SquareOccurs (candidate 12 9 1) μ := by
  exact candidate_cone (by decide) degreeCard116 degreePlan116_1 degreeRows116_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

lemma degreeCones116 : ∀ q ∈ degreeQs116, ∀ μ : YoungDiagram, μ.card = 116 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 12 9 1) μ := by
  intro q hq
  simp only [degreeQs116,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone116_1

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos116 (μ : YoungDiagram) (hμ : μ.card = 116) :
    0 < kronecker (canonicalTableau (candidate 12 9 1) degreeCard116)
      (canonicalTableau (candidate 12 9 1) degreeCard116) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 19) (by decide) (by decide) rfl (by decide)
    degreeCard116 degreeRows116_0 (by decide) (by decide)
    degreePlan116_0 (by decide) (by decide) (by decide) (by decide) degreeP116 ?_
    degreeCheck116 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard116 rfl degreeCones116
    degreeTreeAll116 hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Universal tensor squares. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma universal_partition_exceptional_oai (n : ℕ)
    (hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)) :
    ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
  have he := degree_eq n
  rw [staircase_card] at he
  have hcases : n = 71 ∨ n = 73 ∨ n = 75 ∨ n = 77 ∨ n = 79 ∨ n = 81 ∨ n = 83 ∨ n = 85 ∨ n = 87 ∨ n = 89 ∨ n = 106 ∨ n = 108 ∨ n = 110 ∨ n = 112 ∨ n = 114 ∨ n = 116 ∨ n = 118 ∨ n = 149 ∨ n = 151 := by
    unfold exceptionalPair at hexc
    rcases hexc with ⟨hM,hr⟩ | ⟨hM,hr⟩ | ⟨hM,hr⟩ <;>
      rw [hM] at he <;> norm_num at he <;> omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,exceptionalCard71,exceptional_pos71⟩
  · exact ⟨_,exceptionalCard73,exceptional_pos73⟩
  · exact ⟨_,exceptionalCard75,exceptional_pos75⟩
  · exact ⟨_,exceptionalCard77,exceptional_pos77⟩
  · exact ⟨_,exceptionalCard79,exceptional_pos79⟩
  · exact ⟨_,exceptionalCard81,exceptional_pos81⟩
  · exact ⟨_,exceptionalCard83,exceptional_pos83⟩
  · exact ⟨_,exceptionalCard85,exceptional_pos85⟩
  · exact ⟨_,exceptionalCard87,exceptional_pos87⟩
  · exact ⟨_,degreeCard89,degree_pos89⟩
  · exact ⟨_,exceptionalCard106,exceptional_pos106⟩
  · exact ⟨_,exceptionalCard108,exceptional_pos108⟩
  · exact ⟨_,exceptionalCard110,exceptional_pos110⟩
  · exact ⟨_,degreeCard112,degree_pos112⟩
  · exact ⟨_,exceptionalCard114,exceptional_pos114⟩
  · exact ⟨_,degreeCard116,degree_pos116⟩
  · exact ⟨_,degreeCard118,degree_pos118⟩
  · exact ⟨_,exceptionalCard149,exceptional_pos149⟩
  · exact ⟨_,degreeCard151,degree_pos151⟩

universe u

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.universal_partition_exceptional_oai := @OAI.UniversalTensorSquare.universal_partition_exceptional_oai
