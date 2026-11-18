-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23275
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:09:15.819699+00:00
-- url     : https://prove2.me/submissions/9e34d131-abc1-41db-8996-9808d18249ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6443
import Theorems.Thm_OAI_UniversalTensorSquare_sg6790

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23275_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6443 sg6790

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23275_oai := @OAI.UniversalTensorSquare.sg23275_oai
