-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33758
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:47.399676+00:00
-- url     : https://prove2.me/submissions/4465b017-73a7-406b-bc2c-c27c9fb64276

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17310
import Theorems.Thm_OAI_UniversalTensorSquare_sg20505

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33758_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20505 sg17310

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33758_oai := @OAI.UniversalTensorSquare.sg33758_oai
