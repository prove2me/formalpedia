-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos48
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:33.438591+00:00
-- url     : https://prove2.me/submissions/8dde2b11-57b0-430d-afc5-617d31b292e9
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones48 : ∀ q ∈ degreeQs48, ∀ μ : YoungDiagram, μ.card = 48 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 3 0) μ := by
  intro q hq
  simp only [degreeQs48,List.not_mem_nil] at hq

lemma degreeCheck48_0_0 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 1 1 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_0_1 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 1 2 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_0_2 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 1 3 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_0_3 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 1 4 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_0_4 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 1 5 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_1_0 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 2 1 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_1_1 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 2 2 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_1_2 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 2 3 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_1_3 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 2 4 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_1_4 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 2 5 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_2_0 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 3 1 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_2_1 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 3 2 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_2_2 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 3 3 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_2_3 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 3 4 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_2_4 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 3 5 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_3_0 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 4 1 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_3_1 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 4 2 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_3_2 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 4 3 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_3_3 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 4 4 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_3_4 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 4 5 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_4_0 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 5 1 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_4_1 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 5 2 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_4_2 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 5 3 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_4_3 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 5 4 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48_4_4 :
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 5 5 (a+1) (c+1) degreeRows48_0 degreeP48 := by
  decide +kernel

lemma degreeCheck48 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows48_0.length, ∀ c ∈ List.range degreeRows48_0.length,
      residualCheck 48 8 6 (d+1) (e+1) (a+1) (c+1) degreeRows48_0 degreeP48 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck48_0_0
  · exact degreeCheck48_0_1
  · exact degreeCheck48_0_2
  · exact degreeCheck48_0_3
  · exact degreeCheck48_0_4
  · exact degreeCheck48_1_0
  · exact degreeCheck48_1_1
  · exact degreeCheck48_1_2
  · exact degreeCheck48_1_3
  · exact degreeCheck48_1_4
  · exact degreeCheck48_2_0
  · exact degreeCheck48_2_1
  · exact degreeCheck48_2_2
  · exact degreeCheck48_2_3
  · exact degreeCheck48_2_4
  · exact degreeCheck48_3_0
  · exact degreeCheck48_3_1
  · exact degreeCheck48_3_2
  · exact degreeCheck48_3_3
  · exact degreeCheck48_3_4
  · exact degreeCheck48_4_0
  · exact degreeCheck48_4_1
  · exact degreeCheck48_4_2
  · exact degreeCheck48_4_3
  · exact degreeCheck48_4_4

lemma degree_pos48_oai (μ : YoungDiagram) (hμ : μ.card = 48) :
    0 < kronecker (canonicalTableau (candidate 8 3 0) degreeCard48)
      (canonicalTableau (candidate 8 3 0) degreeCard48) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 6) (by decide) (by decide) rfl (by decide)
    degreeCard48 degreeRows48_0 (by decide) (by decide)
    degreePlan48_0 (by decide) (by decide) (by decide) (by decide) degreeP48 ?_
    degreeCheck48 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard48 rfl degreeCones48
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos48_oai := @OAI.UniversalTensorSquare.degree_pos48_oai
