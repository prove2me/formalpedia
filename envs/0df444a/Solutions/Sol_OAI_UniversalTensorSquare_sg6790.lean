-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6790
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:10:18.875406+00:00
-- url     : https://prove2.me/submissions/c74eef04-5956-458e-865d-1b058c8a2d14

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1002
import Theorems.Thm_OAI_UniversalTensorSquare_sg958

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6790_oai : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg958 sg1002

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6790_oai := @OAI.UniversalTensorSquare.sg6790_oai
