-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos61
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:46.797145+00:00
-- url     : https://prove2.me/submissions/2d477655-acfd-42a7-873f-d55d22d575be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones61 : ∀ q ∈ degreeQs61, ∀ μ : YoungDiagram, μ.card = 61 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 1 1) μ := by
  intro q hq
  simp only [degreeQs61,List.not_mem_nil] at hq

lemma degreeCheck61_0_0 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 1 1 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_0_1 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 1 2 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_0_2 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 1 3 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_0_3 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 1 4 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_0_4 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 1 5 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_1_0 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 2 1 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_1_1 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 2 2 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_1_2 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 2 3 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_1_3 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 2 4 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_1_4 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 2 5 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_2_0 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 3 1 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_2_1 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 3 2 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_2_2 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 3 3 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_2_3 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 3 4 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_2_4 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 3 5 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_3_0 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 4 1 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_3_1 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 4 2 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_3_2 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 4 3 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_3_3 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 4 4 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_3_4 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 4 5 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_4_0 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 5 1 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_4_1 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 5 2 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_4_2 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 5 3 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_4_3 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 5 4 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61_4_4 :
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 5 5 (a+1) (c+1) degreeRows61_0 degreeP61 := by
  decide +kernel

lemma degreeCheck61 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows61_0.length, ∀ c ∈ List.range degreeRows61_0.length,
      residualCheck 61 10 3 (d+1) (e+1) (a+1) (c+1) degreeRows61_0 degreeP61 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck61_0_0
  · exact degreeCheck61_0_1
  · exact degreeCheck61_0_2
  · exact degreeCheck61_0_3
  · exact degreeCheck61_0_4
  · exact degreeCheck61_1_0
  · exact degreeCheck61_1_1
  · exact degreeCheck61_1_2
  · exact degreeCheck61_1_3
  · exact degreeCheck61_1_4
  · exact degreeCheck61_2_0
  · exact degreeCheck61_2_1
  · exact degreeCheck61_2_2
  · exact degreeCheck61_2_3
  · exact degreeCheck61_2_4
  · exact degreeCheck61_3_0
  · exact degreeCheck61_3_1
  · exact degreeCheck61_3_2
  · exact degreeCheck61_3_3
  · exact degreeCheck61_3_4
  · exact degreeCheck61_4_0
  · exact degreeCheck61_4_1
  · exact degreeCheck61_4_2
  · exact degreeCheck61_4_3
  · exact degreeCheck61_4_4

lemma degree_pos61_oai (μ : YoungDiagram) (hμ : μ.card = 61) :
    0 < kronecker (canonicalTableau (candidate 10 1 1) degreeCard61)
      (canonicalTableau (candidate 10 1 1) degreeCard61) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard61 degreeRows61_0 (by decide) (by decide)
    degreePlan61_0 (by decide) (by decide) (by decide) (by decide) degreeP61 ?_
    degreeCheck61 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard61 rfl degreeCones61
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos61_oai := @OAI.UniversalTensorSquare.degree_pos61_oai
