-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8708
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:27:34.375854+00:00
-- url     : https://prove2.me/submissions/963d581a-95fd-4259-b554-29d0287543c9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1338
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8708_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg892 sg1338

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8708_oai := @OAI.UniversalTensorSquare.sg8708_oai
