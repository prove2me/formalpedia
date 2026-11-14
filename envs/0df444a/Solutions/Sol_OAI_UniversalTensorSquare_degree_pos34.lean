-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos34
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:20.003758+00:00
-- url     : https://prove2.me/submissions/e7fd3abe-0bcc-4b70-878b-1a2e8ad84cd1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones34 : ∀ q ∈ degreeQs34, ∀ μ : YoungDiagram, μ.card = 34 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 7 1 1) μ := by
  intro q hq
  simp only [degreeQs34,List.not_mem_nil] at hq

lemma degreeCheck34_0_0 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 1 1 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_0_1 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 1 2 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_0_2 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 1 3 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_0_3 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 1 4 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_0_4 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 1 5 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_1_0 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 2 1 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_1_1 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 2 2 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_1_2 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 2 3 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_1_3 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 2 4 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_1_4 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 2 5 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_2_0 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 3 1 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_2_1 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 3 2 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_2_2 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 3 3 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_2_3 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 3 4 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_2_4 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 3 5 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_3_0 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 4 1 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_3_1 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 4 2 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_3_2 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 4 3 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_3_3 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 4 4 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_3_4 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 4 5 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_4_0 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 5 1 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_4_1 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 5 2 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_4_2 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 5 3 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_4_3 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 5 4 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34_4_4 :
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 5 5 (a+1) (c+1) degreeRows34_0 degreeP34 := by
  decide +kernel

lemma degreeCheck34 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows34_0.length, ∀ c ∈ List.range degreeRows34_0.length,
      residualCheck 34 7 3 (d+1) (e+1) (a+1) (c+1) degreeRows34_0 degreeP34 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck34_0_0
  · exact degreeCheck34_0_1
  · exact degreeCheck34_0_2
  · exact degreeCheck34_0_3
  · exact degreeCheck34_0_4
  · exact degreeCheck34_1_0
  · exact degreeCheck34_1_1
  · exact degreeCheck34_1_2
  · exact degreeCheck34_1_3
  · exact degreeCheck34_1_4
  · exact degreeCheck34_2_0
  · exact degreeCheck34_2_1
  · exact degreeCheck34_2_2
  · exact degreeCheck34_2_3
  · exact degreeCheck34_2_4
  · exact degreeCheck34_3_0
  · exact degreeCheck34_3_1
  · exact degreeCheck34_3_2
  · exact degreeCheck34_3_3
  · exact degreeCheck34_3_4
  · exact degreeCheck34_4_0
  · exact degreeCheck34_4_1
  · exact degreeCheck34_4_2
  · exact degreeCheck34_4_3
  · exact degreeCheck34_4_4

lemma degree_pos34_oai (μ : YoungDiagram) (hμ : μ.card = 34) :
    0 < kronecker (canonicalTableau (candidate 7 1 1) degreeCard34)
      (canonicalTableau (candidate 7 1 1) degreeCard34) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard34 degreeRows34_0 (by decide) (by decide)
    degreePlan34_0 (by decide) (by decide) (by decide) (by decide) degreeP34 ?_
    degreeCheck34 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard34 rfl degreeCones34
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos34_oai := @OAI.UniversalTensorSquare.degree_pos34_oai
