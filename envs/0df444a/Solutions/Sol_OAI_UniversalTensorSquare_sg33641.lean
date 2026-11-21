-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33641
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T07:08:15.845488+00:00
-- url     : https://prove2.me/submissions/f6eed7b4-aa57-4871-a60c-74299b0a6861

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17293
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 82. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33641_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,8,8,8,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17293

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33641_oai := @OAI.UniversalTensorSquare.sg33641_oai
