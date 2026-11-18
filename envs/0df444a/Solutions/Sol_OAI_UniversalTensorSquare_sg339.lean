-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg339
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:35.468204+00:00
-- url     : https://prove2.me/submissions/462e1cd7-f2a9-418d-989e-bbd424d7a335

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
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

lemma sg339_oai : RowSquare [4,2,1,1] [3,3,2] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [3,3,2])
  have hh : SquareOccurs eightWitness (rowDiagram [3,3,2]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [3,3,2]),
      eight_kronecker_pos _ (rowDiagram_card [3,3,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,2])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg339_oai := @OAI.UniversalTensorSquare.sg339_oai
