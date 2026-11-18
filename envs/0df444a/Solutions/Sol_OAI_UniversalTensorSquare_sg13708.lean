-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg13708
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T13:23:02.298198+00:00
-- url     : https://prove2.me/submissions/5fbf3df3-455d-4f9c-9e49-06bfa100c3f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1893
import Theorems.Thm_OAI_UniversalTensorSquare_sg3655

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13708_oai : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1893 sg3655

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg13708_oai := @OAI.UniversalTensorSquare.sg13708_oai
