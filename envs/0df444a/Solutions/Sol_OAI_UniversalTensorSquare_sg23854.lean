-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23854
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:14:59.513196+00:00
-- url     : https://prove2.me/submissions/c5c2a124-9d34-4956-9cf8-31561ffd00ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10276
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23854_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10276

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23854_oai := @OAI.UniversalTensorSquare.sg23854_oai
