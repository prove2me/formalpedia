-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:29:16.981562+00:00
-- url     : https://prove2.me/submissions/5258a538-7b2a-47bc-824d-54aa2b158d70

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_0_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_0_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_0_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_0_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_0_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_1_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_1_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_1_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_1_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_1_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck50_2_0

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck50_2_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 (d+1) (e+1) (a+1) (c+1) degreeRows50_0 degreeP50 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck50_0_0
  · exact degreeCheck50_0_1
  · exact degreeCheck50_0_2
  · exact degreeCheck50_0_3
  · exact degreeCheck50_0_4
  · exact degreeCheck50_1_0
  · exact degreeCheck50_1_1
  · exact degreeCheck50_1_2
  · exact degreeCheck50_1_3
  · exact degreeCheck50_1_4
  · exact degreeCheck50_2_0
  · exact degreeCheck50_2_1
  · exact degreeCheck50_2_2
  · exact degreeCheck50_2_3
  · exact degreeCheck50_2_4
  · exact degreeCheck50_3_0
  · exact degreeCheck50_3_1
  · exact degreeCheck50_3_2
  · exact degreeCheck50_3_3
  · exact degreeCheck50_3_4
  · exact degreeCheck50_4_0
  · exact degreeCheck50_4_1
  · exact degreeCheck50_4_2
  · exact degreeCheck50_4_3
  · exact degreeCheck50_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck50_oai := @OAI.UniversalTensorSquare.degreeCheck50_oai
