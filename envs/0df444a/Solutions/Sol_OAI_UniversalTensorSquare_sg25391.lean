-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25391
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:48:31.555133+00:00
-- url     : https://prove2.me/submissions/838cc15f-d8ba-46ff-a821-97868ba5e8aa

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10253
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418

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

lemma sg25391_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10253

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25391_oai := @OAI.UniversalTensorSquare.sg25391_oai
