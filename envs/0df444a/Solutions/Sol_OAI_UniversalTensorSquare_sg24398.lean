-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24398
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:18:16.733994+00:00
-- url     : https://prove2.me/submissions/ebed1305-b620-4c68-a512-9bd2df598aad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg74

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

lemma sg182 : RowSquare [4,1,1,1] [3,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [3,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1,1,1])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3222 : RowSquare [4,4,1,1,1,1,1,1,1] [5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg182 sg373

lemma sg3286 : RowSquare [5,4,1,1,1,1,1,1] [4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg66 sg590

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15692 : RowSquare [9,8,2,2,2,2,2,2,1] [5,5,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3286 sg3222

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21621 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,6,6,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg15692

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24398_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg21621

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24398_oai := @OAI.UniversalTensorSquare.sg24398_oai
