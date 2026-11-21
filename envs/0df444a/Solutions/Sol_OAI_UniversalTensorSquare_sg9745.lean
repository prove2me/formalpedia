-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9745
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:06:53.565372+00:00
-- url     : https://prove2.me/submissions/377df4e8-1631-493e-884a-2bffb1460ed9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1767
import Theorems.Thm_OAI_UniversalTensorSquare_sg998
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9745_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1767

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9745_oai := @OAI.UniversalTensorSquare.sg9745_oai
