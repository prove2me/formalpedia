-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21997
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:47:46.748144+00:00
-- url     : https://prove2.me/submissions/e1fa9ca6-5e80-4df6-bb2d-e90cdfae0571
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6315
import Theorems.Thm_OAI_UniversalTensorSquare_sg7307

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

lemma sg21997_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7307

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21997_oai := @OAI.UniversalTensorSquare.sg21997_oai
