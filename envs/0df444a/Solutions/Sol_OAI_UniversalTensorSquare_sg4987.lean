-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4987
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:34:45.133203+00:00
-- url     : https://prove2.me/submissions/04748cc5-e720-492e-a2da-a6530a261153

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg356
import Theorems.Thm_OAI_UniversalTensorSquare_sg588

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4987_oai : RowSquare [9,4,2,1,1] [4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg356 sg588

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4987_oai := @OAI.UniversalTensorSquare.sg4987_oai
