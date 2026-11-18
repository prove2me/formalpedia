-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:32:15.805265+00:00
-- url     : https://prove2.me/submissions/010478b5-cb82-4343-adf4-4c2c77b164ad

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_Columns_polytabloid_placed_expansion
import Theorems.Thm_OAI_Saxl_intertwiningLiftSubrep_injective
import Theorems.Thm_OAI_Saxl_kronecker_pos_of_contraction
import Theorems.Thm_OAI_Saxl_orbitAverage_base
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts
import Theorems.Thm_OAI_UniversalTensorSquare_certificate5
import Theorems.Thm_OAI_UniversalTensorSquare_eq_diagramOfCols
import Theorems.Thm_OAI_UniversalTensorSquare_fiveWitness_self
import Theorems.Thm_OAI_UniversalTensorSquare_five_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive311
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive32
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive41
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive5
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive_certificate
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive_target_eq
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_partitionLists_five
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowLens_mem_partitionLists

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35_oai : RowSquare [3,1,1] [3,1,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [3,1,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [3,1,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [3,1,1]),
      five_kronecker_pos _ (rowDiagram_card [3,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35_oai := @OAI.UniversalTensorSquare.sg35_oai
