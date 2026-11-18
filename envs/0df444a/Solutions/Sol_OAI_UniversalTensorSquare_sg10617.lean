-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10617
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:48:06.944979+00:00
-- url     : https://prove2.me/submissions/a72dc53e-b191-4cc3-91f9-b1599484ee61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2260
import Theorems.Thm_OAI_UniversalTensorSquare_sg587

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10617_oai : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg2260

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10617_oai := @OAI.UniversalTensorSquare.sg10617_oai
