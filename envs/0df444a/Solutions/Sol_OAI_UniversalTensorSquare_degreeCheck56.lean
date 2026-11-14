-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck56
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:35:20.332743+00:00
-- url     : https://prove2.me/submissions/21f0cbf2-fc36-4ec6-946c-e9e1f4e01504

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_0_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_0_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_0_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_0_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_0_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_1_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_1_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_1_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_1_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_1_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_2_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_2_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_2_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_2_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_2_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_3_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_3_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck56_3_2

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck56_3_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_3_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_0 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 1 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_1 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 2 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_2 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 (d+1) (e+1) (a+1) (c+1) degreeRows56_0 degreeP56 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck56_0_0
  · exact degreeCheck56_0_1
  · exact degreeCheck56_0_2
  · exact degreeCheck56_0_3
  · exact degreeCheck56_0_4
  · exact degreeCheck56_1_0
  · exact degreeCheck56_1_1
  · exact degreeCheck56_1_2
  · exact degreeCheck56_1_3
  · exact degreeCheck56_1_4
  · exact degreeCheck56_2_0
  · exact degreeCheck56_2_1
  · exact degreeCheck56_2_2
  · exact degreeCheck56_2_3
  · exact degreeCheck56_2_4
  · exact degreeCheck56_3_0
  · exact degreeCheck56_3_1
  · exact degreeCheck56_3_2
  · exact degreeCheck56_3_3
  · exact degreeCheck56_3_4
  · exact degreeCheck56_4_0
  · exact degreeCheck56_4_1
  · exact degreeCheck56_4_2
  · exact degreeCheck56_4_3
  · exact degreeCheck56_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck56_oai := @OAI.UniversalTensorSquare.degreeCheck56_oai
