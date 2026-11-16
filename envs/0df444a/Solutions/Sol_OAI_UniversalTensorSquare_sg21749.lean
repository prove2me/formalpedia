-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21749
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T03:11:58.729208+00:00
-- url     : https://prove2.me/submissions/d31ec03c-4523-4b1b-acf2-ee6612b5d53e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sg330 : RowSquare [4,2,1,1] [1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [1,1,1,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [1,1,1,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg914 : RowSquare [5,2,1,1,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg52

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4777 : RowSquare [5,4,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6414 : RowSquare [6,5,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg4777

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6786 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg914

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21749_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6786

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21749_oai := @OAI.UniversalTensorSquare.sg21749_oai
