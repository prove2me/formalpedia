-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39524
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:39:45.908098+00:00
-- url     : https://prove2.me/submissions/f2b96ec6-dac6-41e3-a4cf-2bbd97b4959c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16334
import Theorems.Thm_OAI_UniversalTensorSquare_sg20710

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 97. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39524_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,8,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16334

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39524_oai := @OAI.UniversalTensorSquare.sg39524_oai
