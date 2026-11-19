-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14132
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:19:48.844651+00:00
-- url     : https://prove2.me/submissions/97661e4a-58de-4583-af98-c91d2f146f12

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2297
import Theorems.Thm_OAI_UniversalTensorSquare_sg2959

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14132_oai : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2297 sg2959

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14132_oai := @OAI.UniversalTensorSquare.sg14132_oai
