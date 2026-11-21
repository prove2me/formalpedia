-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9756
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:07:34.001207+00:00
-- url     : https://prove2.me/submissions/a894c6eb-d67b-44b7-a060-e9d367598e68

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg1378
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

lemma sg9756_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1378

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9756_oai := @OAI.UniversalTensorSquare.sg9756_oai
