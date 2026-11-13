-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck151
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:25.212126+00:00
-- url     : https://prove2.me/submissions/6e412a08-c83e-49a9-b397-8631fa9272e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_2_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_2_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_2_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_2_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_2_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_3_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_3_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_3_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_3_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_3_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_4_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_4_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_4_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_4_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_4_4

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck151_0_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 (d+1) (e+1) (a+1) (c+1) degreeRows151_0 degreeP151 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck151_0_0
  · exact degreeCheck151_0_1
  · exact degreeCheck151_0_2
  · exact degreeCheck151_0_3
  · exact degreeCheck151_0_4
  · exact degreeCheck151_1_0
  · exact degreeCheck151_1_1
  · exact degreeCheck151_1_2
  · exact degreeCheck151_1_3
  · exact degreeCheck151_1_4
  · exact degreeCheck151_2_0
  · exact degreeCheck151_2_1
  · exact degreeCheck151_2_2
  · exact degreeCheck151_2_3
  · exact degreeCheck151_2_4
  · exact degreeCheck151_3_0
  · exact degreeCheck151_3_1
  · exact degreeCheck151_3_2
  · exact degreeCheck151_3_3
  · exact degreeCheck151_3_4
  · exact degreeCheck151_4_0
  · exact degreeCheck151_4_1
  · exact degreeCheck151_4_2
  · exact degreeCheck151_4_3
  · exact degreeCheck151_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck151_oai := @OAI.UniversalTensorSquare.degreeCheck151_oai
