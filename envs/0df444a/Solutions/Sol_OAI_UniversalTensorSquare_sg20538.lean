-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20538
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:29:38.851921+00:00
-- url     : https://prove2.me/submissions/92b30208-cc1c-42bb-8fa4-323b850b3aef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1188
import Theorems.Thm_OAI_UniversalTensorSquare_sg8000

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20538_oai : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1188 sg8000

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20538_oai := @OAI.UniversalTensorSquare.sg20538_oai
