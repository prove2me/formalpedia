-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos32
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:14.757207+00:00
-- url     : https://prove2.me/submissions/f494e1d4-5465-4b4b-8422-d9f4f1a24799
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones32 : ∀ q ∈ degreeQs32, ∀ μ : YoungDiagram, μ.card = 32 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 7 1 0) μ := by
  intro q hq
  simp only [degreeQs32,List.not_mem_nil] at hq

lemma degreeCheck32_0_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 (d+1) (e+1) (a+1) (c+1) degreeRows32_0 degreeP32 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck32_0_0
  · exact degreeCheck32_0_1
  · exact degreeCheck32_0_2
  · exact degreeCheck32_0_3
  · exact degreeCheck32_0_4
  · exact degreeCheck32_1_0
  · exact degreeCheck32_1_1
  · exact degreeCheck32_1_2
  · exact degreeCheck32_1_3
  · exact degreeCheck32_1_4
  · exact degreeCheck32_2_0
  · exact degreeCheck32_2_1
  · exact degreeCheck32_2_2
  · exact degreeCheck32_2_3
  · exact degreeCheck32_2_4
  · exact degreeCheck32_3_0
  · exact degreeCheck32_3_1
  · exact degreeCheck32_3_2
  · exact degreeCheck32_3_3
  · exact degreeCheck32_3_4
  · exact degreeCheck32_4_0
  · exact degreeCheck32_4_1
  · exact degreeCheck32_4_2
  · exact degreeCheck32_4_3
  · exact degreeCheck32_4_4

lemma degree_pos32_oai (μ : YoungDiagram) (hμ : μ.card = 32) :
    0 < kronecker (canonicalTableau (candidate 7 1 0) degreeCard32)
      (canonicalTableau (candidate 7 1 0) degreeCard32) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard32 degreeRows32_0 (by decide) (by decide)
    degreePlan32_0 (by decide) (by decide) (by decide) (by decide) degreeP32 ?_
    degreeCheck32 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard32 rfl degreeCones32
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos32_oai := @OAI.UniversalTensorSquare.degree_pos32_oai
