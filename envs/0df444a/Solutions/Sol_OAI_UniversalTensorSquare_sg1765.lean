-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1765
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:10:46.964222+00:00
-- url     : https://prove2.me/submissions/9b08c7ed-859e-4836-8851-8b77ef436546

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg262

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1765_oai : RowSquare [6,2,1,1,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg262

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1765_oai := @OAI.UniversalTensorSquare.sg1765_oai
