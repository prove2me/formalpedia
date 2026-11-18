-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42459
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:26:58.836172+00:00
-- url     : https://prove2.me/submissions/a54bb03d-6985-478f-8918-4f89e1bf85d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16446
import Theorems.Thm_OAI_UniversalTensorSquare_sg20713

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 104. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42459_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16446

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42459_oai := @OAI.UniversalTensorSquare.sg42459_oai
