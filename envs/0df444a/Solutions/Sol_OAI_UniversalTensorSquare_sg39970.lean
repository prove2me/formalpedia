-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39970
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:40:16.449528+00:00
-- url     : https://prove2.me/submissions/c33be2ba-8d5b-45a1-a7e5-c2b84f29c365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15774
import Theorems.Thm_OAI_UniversalTensorSquare_sg20864
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 98. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39970_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,9,8,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20864 sg15774

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39970_oai := @OAI.UniversalTensorSquare.sg39970_oai
