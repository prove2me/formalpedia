-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg22411
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T05:40:45.172196+00:00
-- url     : https://prove2.me/submissions/a58d624d-70e6-49f8-af3e-f2c82a0d96d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6315
import Theorems.Thm_OAI_UniversalTensorSquare_sg7360

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22411_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,9,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7360

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg22411_oai := @OAI.UniversalTensorSquare.sg22411_oai
