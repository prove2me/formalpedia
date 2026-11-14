-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21959
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:47:11.013617+00:00
-- url     : https://prove2.me/submissions/9239092d-a9ff-496e-855a-82216d5e49b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6147
import Theorems.Thm_OAI_UniversalTensorSquare_sg7658

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21959_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7658

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21959_oai := @OAI.UniversalTensorSquare.sg21959_oai
