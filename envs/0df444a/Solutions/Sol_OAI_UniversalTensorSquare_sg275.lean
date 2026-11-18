-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg275
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:27:18.748664+00:00
-- url     : https://prove2.me/submissions/1d69f10a-35ba-4962-beb1-755692cde761
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert275

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

lemma sg275_oai : RowSquare [3,2,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB275 sgT275 sgFlag275
  change solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 ≠ 0
  rw [sgCert275]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg275_oai := @OAI.UniversalTensorSquare.sg275_oai
