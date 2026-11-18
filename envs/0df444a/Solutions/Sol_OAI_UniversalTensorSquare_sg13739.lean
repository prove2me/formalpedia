-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg13739
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T13:23:06.150528+00:00
-- url     : https://prove2.me/submissions/8cdab421-8e9f-42c8-842a-f557a6ca77f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1895
import Theorems.Thm_OAI_UniversalTensorSquare_sg3655

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13739_oai : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg1895 sg3655

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg13739_oai := @OAI.UniversalTensorSquare.sg13739_oai
