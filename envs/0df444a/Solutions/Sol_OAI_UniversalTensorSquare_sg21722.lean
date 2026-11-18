-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21722
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:56:28.879065+00:00
-- url     : https://prove2.me/submissions/d7cbf0e8-9915-4693-a7c8-868a7caeae2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg6151
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

lemma sg21722_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7565

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21722_oai := @OAI.UniversalTensorSquare.sg21722_oai
