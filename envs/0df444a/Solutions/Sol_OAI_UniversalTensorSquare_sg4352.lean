-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4352
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:24:55.644935+00:00
-- url     : https://prove2.me/submissions/f3aa81af-59d3-4747-85e9-d4330d603791
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg231
import Theorems.Thm_OAI_UniversalTensorSquare_sg428

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4352_oai : RowSquare [8,2,1,1,1,1,1,1] [3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg231 sg428

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4352_oai := @OAI.UniversalTensorSquare.sg4352_oai
