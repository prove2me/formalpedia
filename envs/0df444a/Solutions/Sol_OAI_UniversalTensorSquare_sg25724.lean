-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25724
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:18:45.760242+00:00
-- url     : https://prove2.me/submissions/33d6115f-c573-4cc5-b1a6-49f0b6944c80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10273
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25724_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10273

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25724_oai := @OAI.UniversalTensorSquare.sg25724_oai
