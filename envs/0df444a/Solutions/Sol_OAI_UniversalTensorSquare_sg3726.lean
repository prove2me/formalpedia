-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3726
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:20:24.914382+00:00
-- url     : https://prove2.me/submissions/aa57d696-a400-4d95-9e11-2470bedd1ed8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg32

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3726_oai : RowSquare [9,3,2,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1033

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3726_oai := @OAI.UniversalTensorSquare.sg3726_oai
