-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38469
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:16:43.408377+00:00
-- url     : https://prove2.me/submissions/bafcb22c-1d16-49e2-bdd7-5f8a524f0477

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17456
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 94. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38469_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,6,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17456

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38469_oai := @OAI.UniversalTensorSquare.sg38469_oai
