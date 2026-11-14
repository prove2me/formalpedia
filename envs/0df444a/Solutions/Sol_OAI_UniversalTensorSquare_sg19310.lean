-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg19310
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T01:17:47.909987+00:00
-- url     : https://prove2.me/submissions/4b6fac1d-78ab-4c12-b1e3-92cf76511219
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg15129

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19310_oai : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15129

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg19310_oai := @OAI.UniversalTensorSquare.sg19310_oai
