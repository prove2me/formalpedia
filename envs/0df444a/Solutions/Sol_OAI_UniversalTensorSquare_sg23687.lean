-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23687
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:32:03.017354+00:00
-- url     : https://prove2.me/submissions/4c29a56b-00a2-488b-9832-33c758013f6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12931
import Theorems.Thm_OAI_UniversalTensorSquare_sg4747

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

lemma sg23687_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4747 sg12931

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23687_oai := @OAI.UniversalTensorSquare.sg23687_oai
