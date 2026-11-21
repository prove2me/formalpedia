-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39870
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:55.151586+00:00
-- url     : https://prove2.me/submissions/39e6bd03-47de-48d9-9c84-449375233564

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16334
import Theorems.Thm_OAI_UniversalTensorSquare_sg20713

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 98. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39870_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,8,8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16334

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39870_oai := @OAI.UniversalTensorSquare.sg39870_oai
