-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1287
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T19:49:44.837591+00:00
-- url     : https://prove2.me/submissions/13d4423b-fc5b-4334-a7e9-f4cad407f786

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg115
import Theorems.Thm_OAI_UniversalTensorSquare_sg17

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1287_oai : RowSquare [5,3,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg17 sg115

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1287_oai := @OAI.UniversalTensorSquare.sg1287_oai
