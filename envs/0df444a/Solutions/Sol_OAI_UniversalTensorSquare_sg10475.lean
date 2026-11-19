-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10475
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:15:09.975202+00:00
-- url     : https://prove2.me/submissions/a7928dbe-2215-4ff6-ad6f-64262d9b4379

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg6996

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10475_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6996

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10475_oai := @OAI.UniversalTensorSquare.sg10475_oai
