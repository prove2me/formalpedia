-- Prove2me | solution 1 for OAI.UniversalTensorSquare.five_kronecker_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:53:54.706015+00:00
-- url     : https://prove2.me/submissions/7b028c60-1f25-4a8b-b0e4-7dfe2fead840

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_eq_diagramOfCols
import Theorems.Thm_OAI_UniversalTensorSquare_fiveWitness_self
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive311
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive32
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive41
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive5
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive_target_eq
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_partitionLists_five
import Theorems.Thm_OAI_UniversalTensorSquare_rowLens_mem_partitionLists

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeFive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Five. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

theorem five_kronecker_pos_oai (ν : YoungDiagram) (hν : ν.card = 5) :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_five] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [5] (by decide) h
    subst ν
    exact five_positive5
  · have he := eq_diagramOfCols ν [4,1] (by decide) h
    subst ν
    exact five_positive41
  · have he := eq_diagramOfCols ν [3,2] (by decide) h
    subst ν
    exact five_positive32
  · have he := eq_diagramOfCols ν [3,1,1] (by decide) h
    subst ν
    exact five_positive311
  · have he := eq_diagramOfCols ν [2,2,1] (by decide) h
    have ht : diagramOfCols [2,2,1] (by decide) =
        (diagramOfCols [3,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose fiveWitness fiveWitness_card fiveWitness_self
      _ _ five_positive32
    exact five_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [2,1,1,1] (by decide) h
    have ht : diagramOfCols [2,1,1,1] (by decide) =
        (diagramOfCols [4,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose fiveWitness fiveWitness_card fiveWitness_self
      _ _ five_positive41
    exact five_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [1,1,1,1,1] (by decide) h
    have ht : diagramOfCols [1,1,1,1,1] (by decide) =
        (diagramOfCols [5] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose fiveWitness fiveWitness_card fiveWitness_self
      _ _ five_positive5
    exact five_positive_target_eq hν _ (he.trans ht) hh

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.five_kronecker_pos_oai := @OAI.UniversalTensorSquare.five_kronecker_pos_oai
