-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T02:51:35.675543+00:00
-- url     : https://prove2.me/submissions/3fad004c-2213-4e01-8ab9-74e75f90883f

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_five_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq

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

lemma sg32_oai : RowSquare [3,1,1] [1,1,1,1,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [1,1,1,1,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [1,1,1,1,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1]),
      five_kronecker_pos _ (rowDiagram_card [1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32_oai := @OAI.UniversalTensorSquare.sg32_oai
