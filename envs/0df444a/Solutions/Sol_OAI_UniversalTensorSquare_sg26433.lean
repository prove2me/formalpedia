-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26433
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:15:35.188047+00:00
-- url     : https://prove2.me/submissions/223be6fe-cbd6-42fa-933a-d8dfe980bccb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11468
import Theorems.Thm_OAI_UniversalTensorSquare_sg6952

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26433_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6952 sg11468

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26433_oai := @OAI.UniversalTensorSquare.sg26433_oai
