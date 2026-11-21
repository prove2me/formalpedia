-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40614
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T15:45:02.243021+00:00
-- url     : https://prove2.me/submissions/7078fd7f-7f3f-4dd5-8ea7-abeacfd64752

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18703
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 100. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40614_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,7,7,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18703

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40614_oai := @OAI.UniversalTensorSquare.sg40614_oai
