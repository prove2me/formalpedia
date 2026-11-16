-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23293
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:11:07.684465+00:00
-- url     : https://prove2.me/submissions/69a35e77-5965-4668-b08f-8f0bf88c4e50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1015
import Theorems.Thm_OAI_UniversalTensorSquare_sg248
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sg345 : RowSquare [4,2,1,1] [5,3] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [5,3])
  have hh : SquareOccurs eightWitness (rowDiagram [5,3]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [5,3]),
      eight_kronecker_pos _ (rowDiagram_card [5,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,3])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4066 : RowSquare [6,4,2,2,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg345 sg248

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

lemma sg6376 : RowSquare [6,4,2,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4066

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7077 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1015

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23293_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7077

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23293_oai := @OAI.UniversalTensorSquare.sg23293_oai
