-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23431
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T15:42:26.038889+00:00
-- url     : https://prove2.me/submissions/365cbed6-6796-4a46-99ec-2f76b145b0c7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg14308
import Theorems.Thm_OAI_UniversalTensorSquare_sg1817

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23431_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg14308

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23431_oai := @OAI.UniversalTensorSquare.sg23431_oai
