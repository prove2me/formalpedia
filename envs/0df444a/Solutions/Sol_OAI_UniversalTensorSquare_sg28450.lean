-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28450
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T14:36:37.770346+00:00
-- url     : https://prove2.me/submissions/a4389432-1382-437b-b84c-c02cbc49d786
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg21263

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert552 : solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB552 sgT552) sgFlag552 = -1 := by
  decide +kernel

lemma sg552 : RowSquare [4,2,2,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB552 sgT552 sgFlag552
  change solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB552 sgT552) sgFlag552 ≠ 0
  rw [sgCert552]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28450_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,3,3,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg552 sg21263

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28450_oai := @OAI.UniversalTensorSquare.sg28450_oai
