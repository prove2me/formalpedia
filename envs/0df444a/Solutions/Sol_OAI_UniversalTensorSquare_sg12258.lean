-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12258
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:15:29.949791+00:00
-- url     : https://prove2.me/submissions/d0615c05-197b-434f-84a5-43a94239fb00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2585
import Theorems.Thm_OAI_UniversalTensorSquare_sg771

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12258_oai : RowSquare [8,6,2,2,2,2,1,1] [8,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg771 sg2585

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12258_oai := @OAI.UniversalTensorSquare.sg12258_oai
