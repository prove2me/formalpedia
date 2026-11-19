-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6677
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:06:07.314203+00:00
-- url     : https://prove2.me/submissions/93781de8-dccd-4220-a704-c67926a6af17

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1038
import Theorems.Thm_OAI_UniversalTensorSquare_sg943
import Definitions.Def_OAIQ259US001
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

lemma sg6677_oai : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg943

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6677_oai := @OAI.UniversalTensorSquare.sg6677_oai
