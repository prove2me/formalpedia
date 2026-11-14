-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos59
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:44.177837+00:00
-- url     : https://prove2.me/submissions/fdcebe8d-8a27-48e3-b061-443e791e8810
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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones59 : ∀ q ∈ degreeQs59, ∀ μ : YoungDiagram, μ.card = 59 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 1 0) μ := by
  intro q hq
  simp only [degreeQs59,List.not_mem_nil] at hq

lemma degreeCheck59_0_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 (d+1) (e+1) (a+1) (c+1) degreeRows59_0 degreeP59 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck59_0_0
  · exact degreeCheck59_0_1
  · exact degreeCheck59_0_2
  · exact degreeCheck59_0_3
  · exact degreeCheck59_0_4
  · exact degreeCheck59_1_0
  · exact degreeCheck59_1_1
  · exact degreeCheck59_1_2
  · exact degreeCheck59_1_3
  · exact degreeCheck59_1_4
  · exact degreeCheck59_2_0
  · exact degreeCheck59_2_1
  · exact degreeCheck59_2_2
  · exact degreeCheck59_2_3
  · exact degreeCheck59_2_4
  · exact degreeCheck59_3_0
  · exact degreeCheck59_3_1
  · exact degreeCheck59_3_2
  · exact degreeCheck59_3_3
  · exact degreeCheck59_3_4
  · exact degreeCheck59_4_0
  · exact degreeCheck59_4_1
  · exact degreeCheck59_4_2
  · exact degreeCheck59_4_3
  · exact degreeCheck59_4_4

lemma degree_pos59_oai (μ : YoungDiagram) (hμ : μ.card = 59) :
    0 < kronecker (canonicalTableau (candidate 10 1 0) degreeCard59)
      (canonicalTableau (candidate 10 1 0) degreeCard59) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard59 degreeRows59_0 (by decide) (by decide)
    degreePlan59_0 (by decide) (by decide) (by decide) (by decide) degreeP59 ?_
    degreeCheck59 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard59 rfl degreeCones59
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos59_oai := @OAI.UniversalTensorSquare.degree_pos59_oai
