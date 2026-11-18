-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg442
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:30:00.080497+00:00
-- url     : https://prove2.me/submissions/89e66d09-9449-4c04-9922-4f812021a50d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg42

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg442_oai : RowSquare [2,2,2,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg42

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg442_oai := @OAI.UniversalTensorSquare.sg442_oai
