-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg41962
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:48:12.039205+00:00
-- url     : https://prove2.me/submissions/9f9aa619-052c-42b8-b8fd-5bd4d93f7d40

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16409
import Theorems.Thm_OAI_UniversalTensorSquare_sg20713

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 103. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41962_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16409

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg41962_oai := @OAI.UniversalTensorSquare.sg41962_oai
