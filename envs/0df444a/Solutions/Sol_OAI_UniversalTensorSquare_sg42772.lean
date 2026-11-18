-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42772
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:49:53.003096+00:00
-- url     : https://prove2.me/submissions/906b59fa-3e9a-4eaa-af40-dee22a6d299f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16483
import Theorems.Thm_OAI_UniversalTensorSquare_sg20728

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

lemma sg42772_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,7,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20728 sg16483

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42772_oai := @OAI.UniversalTensorSquare.sg42772_oai
