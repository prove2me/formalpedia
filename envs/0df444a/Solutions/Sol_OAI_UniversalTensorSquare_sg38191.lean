-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38191
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:41:31.093442+00:00
-- url     : https://prove2.me/submissions/8a70e1be-b03c-4184-a55c-532248fc0e33

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16278
import Theorems.Thm_OAI_UniversalTensorSquare_sg20716

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

lemma sg38191_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,8,7,7,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16278

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38191_oai := @OAI.UniversalTensorSquare.sg38191_oai
