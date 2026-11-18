-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21738
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:05:30.504082+00:00
-- url     : https://prove2.me/submissions/2c770c03-0d3c-4e31-ba8e-b050959bc248
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6472
import Theorems.Thm_OAI_UniversalTensorSquare_sg6652

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21738_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6652

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21738_oai := @OAI.UniversalTensorSquare.sg21738_oai
