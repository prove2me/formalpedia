-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32362
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T02:58:07.315171+00:00
-- url     : https://prove2.me/submissions/bac06fc0-bcd0-410a-84cc-2df90bafc861

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17208
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32362_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17208

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32362_oai := @OAI.UniversalTensorSquare.sg32362_oai
