-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38190
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:41:26.576286+00:00
-- url     : https://prove2.me/submissions/647660ed-a39a-4324-8718-2fb3924be44e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17422
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515

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

lemma sg38190_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,8,7,7,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17422

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38190_oai := @OAI.UniversalTensorSquare.sg38190_oai
