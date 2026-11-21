-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25472
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:35:31.177627+00:00
-- url     : https://prove2.me/submissions/d73193ba-028d-4392-bfef-759267ef821e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10253
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25472_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10253

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25472_oai := @OAI.UniversalTensorSquare.sg25472_oai
