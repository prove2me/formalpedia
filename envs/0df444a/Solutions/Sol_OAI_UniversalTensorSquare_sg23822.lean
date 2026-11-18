-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23822
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:14:45.930687+00:00
-- url     : https://prove2.me/submissions/af560b30-4648-4ced-9edb-58e9ea11dec1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9712

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23822_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9712

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23822_oai := @OAI.UniversalTensorSquare.sg23822_oai
