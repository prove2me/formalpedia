-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg36104
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T12:46:54.354683+00:00
-- url     : https://prove2.me/submissions/6ff58751-8794-459f-a0e8-bc447c261384
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17230
import Theorems.Thm_OAI_UniversalTensorSquare_sg20529

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 88. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36104_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17230

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg36104_oai := @OAI.UniversalTensorSquare.sg36104_oai
