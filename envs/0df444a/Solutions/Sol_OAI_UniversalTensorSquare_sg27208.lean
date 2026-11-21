-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27208
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T12:08:40.340533+00:00
-- url     : https://prove2.me/submissions/e26a06b5-1b95-4984-b2b2-33b1e41b5cf1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8660
import Theorems.Thm_OAI_UniversalTensorSquare_sg9730

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27208_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9730

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27208_oai := @OAI.UniversalTensorSquare.sg27208_oai
