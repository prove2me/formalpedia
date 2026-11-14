-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos44
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:27.915677+00:00
-- url     : https://prove2.me/submissions/d27ebde3-4bed-4cee-9750-68bb486fb8de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones44 : ∀ q ∈ degreeQs44, ∀ μ : YoungDiagram, μ.card = 44 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 2 0) μ := by
  intro q hq
  simp only [degreeQs44,List.not_mem_nil] at hq

lemma degreeCheck44_0_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 (d+1) (e+1) (a+1) (c+1) degreeRows44_0 degreeP44 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck44_0_0
  · exact degreeCheck44_0_1
  · exact degreeCheck44_0_2
  · exact degreeCheck44_0_3
  · exact degreeCheck44_0_4
  · exact degreeCheck44_1_0
  · exact degreeCheck44_1_1
  · exact degreeCheck44_1_2
  · exact degreeCheck44_1_3
  · exact degreeCheck44_1_4
  · exact degreeCheck44_2_0
  · exact degreeCheck44_2_1
  · exact degreeCheck44_2_2
  · exact degreeCheck44_2_3
  · exact degreeCheck44_2_4
  · exact degreeCheck44_3_0
  · exact degreeCheck44_3_1
  · exact degreeCheck44_3_2
  · exact degreeCheck44_3_3
  · exact degreeCheck44_3_4
  · exact degreeCheck44_4_0
  · exact degreeCheck44_4_1
  · exact degreeCheck44_4_2
  · exact degreeCheck44_4_3
  · exact degreeCheck44_4_4

lemma degree_pos44_oai (μ : YoungDiagram) (hμ : μ.card = 44) :
    0 < kronecker (canonicalTableau (candidate 8 2 0) degreeCard44)
      (canonicalTableau (candidate 8 2 0) degreeCard44) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard44 degreeRows44_0 (by decide) (by decide)
    degreePlan44_0 (by decide) (by decide) (by decide) (by decide) degreeP44 ?_
    degreeCheck44 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard44 rfl degreeCones44
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos44_oai := @OAI.UniversalTensorSquare.degree_pos44_oai
