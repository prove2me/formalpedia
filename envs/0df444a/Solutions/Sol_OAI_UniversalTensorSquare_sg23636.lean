-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23636
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:11:52.139457+00:00
-- url     : https://prove2.me/submissions/9d92ad13-0906-4c74-88a0-fc6e79dd9ef6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6900
import Theorems.Thm_OAI_UniversalTensorSquare_sg8708

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23636_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6900 sg8708

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23636_oai := @OAI.UniversalTensorSquare.sg23636_oai
