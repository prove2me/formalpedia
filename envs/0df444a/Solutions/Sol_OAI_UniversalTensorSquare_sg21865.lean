-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21865
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:56:33.056949+00:00
-- url     : https://prove2.me/submissions/ae9a7a22-22ec-44b2-84b8-d73a22840246
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg6154
import Theorems.Thm_OAI_UniversalTensorSquare_sg6197

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7565 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6197

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21865_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6154 sg7565

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21865_oai := @OAI.UniversalTensorSquare.sg21865_oai
