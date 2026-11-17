-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:38:56.330786+00:00
-- url     : https://prove2.me/submissions/2ab27740-6729-49bc-8898-4516042b231e

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

lemma sg33_oai : RowSquare [3,1,1] [2,1,1,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [2,1,1,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [2,1,1,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1]),
      five_kronecker_pos _ (rowDiagram_card [2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33_oai := @OAI.UniversalTensorSquare.sg33_oai
