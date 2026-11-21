-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27780
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T13:58:36.17944+00:00
-- url     : https://prove2.me/submissions/ac6529ed-8b30-48f8-890f-d8b922630c9c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1328
import Theorems.Thm_OAI_UniversalTensorSquare_sg1335
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468

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

lemma sg10202 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1335

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 68. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27780_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,4,3,3,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10202

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27780_oai := @OAI.UniversalTensorSquare.sg27780_oai
