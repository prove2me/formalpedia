-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck60
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:38:40.865818+00:00
-- url     : https://prove2.me/submissions/f4a75318-f020-4ddf-bc24-dc7e577aea76

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_0_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_0_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_0_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_0_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_0_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_1_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_1_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_1_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_1_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_1_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_2_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_2_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_2_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_2_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_2_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_3_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_3_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_3_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_3_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_3_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_4_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_4_1

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck60_4_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_3 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_4 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 5 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 (d+1) (e+1) (a+1) (c+1) degreeRows60_0 degreeP60 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck60_0_0
  · exact degreeCheck60_0_1
  · exact degreeCheck60_0_2
  · exact degreeCheck60_0_3
  · exact degreeCheck60_0_4
  · exact degreeCheck60_1_0
  · exact degreeCheck60_1_1
  · exact degreeCheck60_1_2
  · exact degreeCheck60_1_3
  · exact degreeCheck60_1_4
  · exact degreeCheck60_2_0
  · exact degreeCheck60_2_1
  · exact degreeCheck60_2_2
  · exact degreeCheck60_2_3
  · exact degreeCheck60_2_4
  · exact degreeCheck60_3_0
  · exact degreeCheck60_3_1
  · exact degreeCheck60_3_2
  · exact degreeCheck60_3_3
  · exact degreeCheck60_3_4
  · exact degreeCheck60_4_0
  · exact degreeCheck60_4_1
  · exact degreeCheck60_4_2
  · exact degreeCheck60_4_3
  · exact degreeCheck60_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck60_oai := @OAI.UniversalTensorSquare.degreeCheck60_oai
