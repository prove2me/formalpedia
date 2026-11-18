-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42704
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:42:19.37002+00:00
-- url     : https://prove2.me/submissions/4e52422f-6156-4d36-b07a-bde3ad21c4d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17839
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 105. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42704_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,5,5,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17839

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42704_oai := @OAI.UniversalTensorSquare.sg42704_oai
