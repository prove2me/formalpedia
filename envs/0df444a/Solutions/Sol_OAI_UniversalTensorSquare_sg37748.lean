-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37748
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:05:35.308582+00:00
-- url     : https://prove2.me/submissions/0b89f37c-1118-4f61-93dc-ae6e91d7ad0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16279
import Theorems.Thm_OAI_UniversalTensorSquare_sg20708

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 93. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37748_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,6,6,6,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20708 sg16279

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37748_oai := @OAI.UniversalTensorSquare.sg37748_oai
