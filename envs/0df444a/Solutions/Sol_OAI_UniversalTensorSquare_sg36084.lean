-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg36084
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T12:46:50.591388+00:00
-- url     : https://prove2.me/submissions/435a276a-8f53-4073-9a58-8fa29d58fcf5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17229
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

lemma sg36084_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17229

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg36084_oai := @OAI.UniversalTensorSquare.sg36084_oai
