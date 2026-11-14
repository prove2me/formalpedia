-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck54
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:31:38.055269+00:00
-- url     : https://prove2.me/submissions/7f492658-a684-4f5c-9bf3-cc9ab74ba72a

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_0_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_0_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_0_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_0_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_0_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_1_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_1_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_1_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_1_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_1_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_2_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_2_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_2_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_2_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_2_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_3_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_3_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck54_3_2

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck54_3_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_3_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_0 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 1 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_1 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 2 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_2 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 3 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 (d+1) (e+1) (a+1) (c+1) degreeRows54_0 degreeP54 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck54_0_0
  · exact degreeCheck54_0_1
  · exact degreeCheck54_0_2
  · exact degreeCheck54_0_3
  · exact degreeCheck54_0_4
  · exact degreeCheck54_1_0
  · exact degreeCheck54_1_1
  · exact degreeCheck54_1_2
  · exact degreeCheck54_1_3
  · exact degreeCheck54_1_4
  · exact degreeCheck54_2_0
  · exact degreeCheck54_2_1
  · exact degreeCheck54_2_2
  · exact degreeCheck54_2_3
  · exact degreeCheck54_2_4
  · exact degreeCheck54_3_0
  · exact degreeCheck54_3_1
  · exact degreeCheck54_3_2
  · exact degreeCheck54_3_3
  · exact degreeCheck54_3_4
  · exact degreeCheck54_4_0
  · exact degreeCheck54_4_1
  · exact degreeCheck54_4_2
  · exact degreeCheck54_4_3
  · exact degreeCheck54_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck54_oai := @OAI.UniversalTensorSquare.degreeCheck54_oai
