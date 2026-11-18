-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25753
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:56:39.956895+00:00
-- url     : https://prove2.me/submissions/30673487-fb7d-449e-9a65-56fe21107145
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10375
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25753_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10375

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25753_oai := @OAI.UniversalTensorSquare.sg25753_oai
