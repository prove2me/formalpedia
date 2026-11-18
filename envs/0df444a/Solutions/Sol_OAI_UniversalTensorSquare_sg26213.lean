-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26213
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:07:07.990337+00:00
-- url     : https://prove2.me/submissions/65174692-5ae1-49b1-968c-d8f28421634a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1358
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10308 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1358

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26213_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10308

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26213_oai := @OAI.UniversalTensorSquare.sg26213_oai
