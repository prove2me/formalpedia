-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg43129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:12:06.438132+00:00
-- url     : https://prove2.me/submissions/adcac839-500c-42c4-b4cd-9d00e8e78f6e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17871
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 106. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg43129_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,8,8,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17871

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg43129_oai := @OAI.UniversalTensorSquare.sg43129_oai
