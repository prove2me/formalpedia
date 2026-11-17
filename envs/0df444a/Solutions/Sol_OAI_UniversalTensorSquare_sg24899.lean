-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24899
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:41:54.528073+00:00
-- url     : https://prove2.me/submissions/f00be411-cec0-47ed-b859-4de4570686e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10240
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24899_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10240

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24899_oai := @OAI.UniversalTensorSquare.sg24899_oai
