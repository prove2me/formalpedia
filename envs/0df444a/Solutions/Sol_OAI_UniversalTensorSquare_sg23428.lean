-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23428
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:24:00.682698+00:00
-- url     : https://prove2.me/submissions/6b6388a5-4c2f-4628-a924-f133c9b58cd1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6148
import Theorems.Thm_OAI_UniversalTensorSquare_sg7765

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23428_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7765

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23428_oai := @OAI.UniversalTensorSquare.sg23428_oai
