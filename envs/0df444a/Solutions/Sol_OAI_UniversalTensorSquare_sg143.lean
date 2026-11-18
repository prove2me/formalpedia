-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg143
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:42:20.447918+00:00
-- url     : https://prove2.me/submissions/e963c626-0d1f-4d59-aa88-a238b223ca8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert143

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg143_oai : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg143_oai := @OAI.UniversalTensorSquare.sg143_oai
