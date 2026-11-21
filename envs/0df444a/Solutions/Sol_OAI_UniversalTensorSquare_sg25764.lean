-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25764
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T09:38:05.495856+00:00
-- url     : https://prove2.me/submissions/22ef9a9e-4a3c-4d08-95f1-e280e6367d72

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10276
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

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

lemma sg25764_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10276

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25764_oai := @OAI.UniversalTensorSquare.sg25764_oai
