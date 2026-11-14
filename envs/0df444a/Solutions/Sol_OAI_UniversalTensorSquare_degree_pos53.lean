-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos53
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:39.045195+00:00
-- url     : https://prove2.me/submissions/d7722c5a-5c82-4636-87a4-dcc658310e58
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones53 : ∀ q ∈ degreeQs53, ∀ μ : YoungDiagram, μ.card = 53 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 2 0) μ := by
  intro q hq
  simp only [degreeQs53,List.not_mem_nil] at hq

lemma degreeCheck53_0_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 (d+1) (e+1) (a+1) (c+1) degreeRows53_0 degreeP53 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck53_0_0
  · exact degreeCheck53_0_1
  · exact degreeCheck53_0_2
  · exact degreeCheck53_0_3
  · exact degreeCheck53_0_4
  · exact degreeCheck53_1_0
  · exact degreeCheck53_1_1
  · exact degreeCheck53_1_2
  · exact degreeCheck53_1_3
  · exact degreeCheck53_1_4
  · exact degreeCheck53_2_0
  · exact degreeCheck53_2_1
  · exact degreeCheck53_2_2
  · exact degreeCheck53_2_3
  · exact degreeCheck53_2_4
  · exact degreeCheck53_3_0
  · exact degreeCheck53_3_1
  · exact degreeCheck53_3_2
  · exact degreeCheck53_3_3
  · exact degreeCheck53_3_4
  · exact degreeCheck53_4_0
  · exact degreeCheck53_4_1
  · exact degreeCheck53_4_2
  · exact degreeCheck53_4_3
  · exact degreeCheck53_4_4

lemma degree_pos53_oai (μ : YoungDiagram) (hμ : μ.card = 53) :
    0 < kronecker (canonicalTableau (candidate 9 2 0) degreeCard53)
      (canonicalTableau (candidate 9 2 0) degreeCard53) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard53 degreeRows53_0 (by decide) (by decide)
    degreePlan53_0 (by decide) (by decide) (by decide) (by decide) degreeP53 ?_
    degreeCheck53 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard53 rfl degreeCones53
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos53_oai := @OAI.UniversalTensorSquare.degree_pos53_oai
