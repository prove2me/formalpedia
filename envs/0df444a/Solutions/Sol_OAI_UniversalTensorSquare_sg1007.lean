-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1007
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:30:24.156719+00:00
-- url     : https://prove2.me/submissions/3639b6a7-b727-4cb9-83a6-a1cf258a6e0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert1007

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1007_oai : RowSquare [6,1,1,1,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1007 sgT1007 sgFlag1007
  change solveCompact 10 (.full [5,3,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB1007 sgT1007) sgFlag1007 ≠ 0
  rw [sgCert1007]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1007_oai := @OAI.UniversalTensorSquare.sg1007_oai
