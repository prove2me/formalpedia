-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos52
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:36.534887+00:00
-- url     : https://prove2.me/submissions/56705fd4-27eb-4a67-8ec5-f6c46d6eb4e3
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones52 : ∀ q ∈ degreeQs52, ∀ μ : YoungDiagram, μ.card = 52 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 4 0) μ := by
  intro q hq
  simp only [degreeQs52, List.not_mem_nil] at hq

lemma degreeCheck52_0_0 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 1 1 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_0_1 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 1 2 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_0_2 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 1 3 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_0_3 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 1 4 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_0_4 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 1 5 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_1_0 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 2 1 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_1_1 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 2 2 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_1_2 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 2 3 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_1_3 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 2 4 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_1_4 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 2 5 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_2_0 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 3 1 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_2_1 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 3 2 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_2_2 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 3 3 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_2_3 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 3 4 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_2_4 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 3 5 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_3_0 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 4 1 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_3_1 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 4 2 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_3_2 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 4 3 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_3_3 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 4 4 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_3_4 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 4 5 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_4_0 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 5 1 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_4_1 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 5 2 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_4_2 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 5 3 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_4_3 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 5 4 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52_4_4 :
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 5 5 (a+1) (c+1) degreeRows52_0 degreeP52 := by
  decide +kernel

lemma degreeCheck52 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows52_0.length, ∀ c ∈ List.range degreeRows52_0.length,
      residualCheck 52 8 8 (d+1) (e+1) (a+1) (c+1) degreeRows52_0 degreeP52 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck52_0_0
  · exact degreeCheck52_0_1
  · exact degreeCheck52_0_2
  · exact degreeCheck52_0_3
  · exact degreeCheck52_0_4
  · exact degreeCheck52_1_0
  · exact degreeCheck52_1_1
  · exact degreeCheck52_1_2
  · exact degreeCheck52_1_3
  · exact degreeCheck52_1_4
  · exact degreeCheck52_2_0
  · exact degreeCheck52_2_1
  · exact degreeCheck52_2_2
  · exact degreeCheck52_2_3
  · exact degreeCheck52_2_4
  · exact degreeCheck52_3_0
  · exact degreeCheck52_3_1
  · exact degreeCheck52_3_2
  · exact degreeCheck52_3_3
  · exact degreeCheck52_3_4
  · exact degreeCheck52_4_0
  · exact degreeCheck52_4_1
  · exact degreeCheck52_4_2
  · exact degreeCheck52_4_3
  · exact degreeCheck52_4_4

lemma degree_pos52_oai (μ : YoungDiagram) (hμ : μ.card = 52) :
    0 < kronecker (canonicalTableau (candidate 8 4 0) degreeCard52)
      (canonicalTableau (candidate 8 4 0) degreeCard52) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 8) (by decide) (by decide) rfl (by decide)
    degreeCard52 degreeRows52_0 (by decide) (by decide)
    degreePlan52_0 (by decide) (by decide) (by decide) (by decide) degreeP52 ?_
    degreeCheck52 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard52 rfl degreeCones52
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos52_oai := @OAI.UniversalTensorSquare.degree_pos52_oai
