-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24287
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:41:17.680113+00:00
-- url     : https://prove2.me/submissions/e7823397-9c75-482f-bf28-d4f34163aed0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10094
import Theorems.Thm_OAI_UniversalTensorSquare_sg8535

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24287_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10094

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24287_oai := @OAI.UniversalTensorSquare.sg24287_oai
