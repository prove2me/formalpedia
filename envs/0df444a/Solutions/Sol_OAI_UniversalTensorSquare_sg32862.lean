-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32862
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T03:55:36.873133+00:00
-- url     : https://prove2.me/submissions/78d6caed-dca1-4cba-9192-e437918a7db7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16237
import Theorems.Thm_OAI_UniversalTensorSquare_sg20710

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 80. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32862_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,8,8,8,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16237

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32862_oai := @OAI.UniversalTensorSquare.sg32862_oai
