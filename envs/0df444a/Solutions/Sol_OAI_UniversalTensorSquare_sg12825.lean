-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12825
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:31:42.57889+00:00
-- url     : https://prove2.me/submissions/67eef78a-9c61-4e0d-bd9b-3192375174c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg4504

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12825_oai : RowSquare [4,4,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1032 sg4504

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12825_oai := @OAI.UniversalTensorSquare.sg12825_oai
