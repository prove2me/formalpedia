-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCover37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:37:32.031634+00:00
-- url     : https://prove2.me/submissions/f2097ad3-f891-469a-b198-afc9d965b127

import Mathlib
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_0_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_0_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_0_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_0_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_0_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_1_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_1_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_1_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_1_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_1_4
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_2_0
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_2_1
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_2_2
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_2_3
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCover37_2_4

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover37_3_0 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 4 1 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_3_1 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 4 2 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_3_2 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 4 3 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_3_3 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 4 4 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_3_4 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 4 5 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_4_0 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 5 1 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_4_1 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 5 2 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_4_2 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 5 3 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_4_3 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 5 4 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_4_4 :
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 5 5 (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  decide +kernel

lemma degreeCover37_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      regionCheck 37 6 8 (d+1) (e+1) (a+1) (c+1) degreeRows37_0 degreeRegions37 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover37_0_0
  · exact degreeCover37_0_1
  · exact degreeCover37_0_2
  · exact degreeCover37_0_3
  · exact degreeCover37_0_4
  · exact degreeCover37_1_0
  · exact degreeCover37_1_1
  · exact degreeCover37_1_2
  · exact degreeCover37_1_3
  · exact degreeCover37_1_4
  · exact degreeCover37_2_0
  · exact degreeCover37_2_1
  · exact degreeCover37_2_2
  · exact degreeCover37_2_3
  · exact degreeCover37_2_4
  · exact degreeCover37_3_0
  · exact degreeCover37_3_1
  · exact degreeCover37_3_2
  · exact degreeCover37_3_3
  · exact degreeCover37_3_4
  · exact degreeCover37_4_0
  · exact degreeCover37_4_1
  · exact degreeCover37_4_2
  · exact degreeCover37_4_3
  · exact degreeCover37_4_4

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCover37_oai := @OAI.UniversalTensorSquare.degreeCover37_oai
