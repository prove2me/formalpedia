-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg17883
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:41:51.037345+00:00
-- url     : https://prove2.me/submissions/eb86198c-b0b1-4d7d-b52c-0c8734976de6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13739
import Theorems.Thm_OAI_UniversalTensorSquare_sg15

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17883_oai : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,5] := by
  exact rowSquare_join (by decide) sg15 sg13739

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg17883_oai := @OAI.UniversalTensorSquare.sg17883_oai
