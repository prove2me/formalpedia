-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23481
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:26:59.878745+00:00
-- url     : https://prove2.me/submissions/fba5bc33-3d12-4c57-bf3b-ca7afcb21d50

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6147
import Theorems.Thm_OAI_UniversalTensorSquare_sg7768

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

lemma sg23481_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7768

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23481_oai := @OAI.UniversalTensorSquare.sg23481_oai
