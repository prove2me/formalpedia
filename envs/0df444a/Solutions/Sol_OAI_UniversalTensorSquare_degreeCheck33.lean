-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:09:01.859111+00:00
-- url     : https://prove2.me/submissions/4a1b19d4-093e-4366-89ae-b1ad65a344e8

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck33_0_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 (d+1) (e+1) (a+1) (c+1) degreeRows33_0 degreeP33 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck33_0_0
  · exact degreeCheck33_0_1
  · exact degreeCheck33_0_2
  · exact degreeCheck33_0_3
  · exact degreeCheck33_0_4
  · exact degreeCheck33_1_0
  · exact degreeCheck33_1_1
  · exact degreeCheck33_1_2
  · exact degreeCheck33_1_3
  · exact degreeCheck33_1_4
  · exact degreeCheck33_2_0
  · exact degreeCheck33_2_1
  · exact degreeCheck33_2_2
  · exact degreeCheck33_2_3
  · exact degreeCheck33_2_4
  · exact degreeCheck33_3_0
  · exact degreeCheck33_3_1
  · exact degreeCheck33_3_2
  · exact degreeCheck33_3_3
  · exact degreeCheck33_3_4
  · exact degreeCheck33_4_0
  · exact degreeCheck33_4_1
  · exact degreeCheck33_4_2
  · exact degreeCheck33_4_3
  · exact degreeCheck33_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck33_oai := @OAI.UniversalTensorSquare.degreeCheck33_oai
