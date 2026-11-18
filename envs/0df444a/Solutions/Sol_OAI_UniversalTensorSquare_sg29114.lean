-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:41:07.306896+00:00
-- url     : https://prove2.me/submissions/34f64ee6-aa2a-42cb-9f39-4847f8df64cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg6942
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

lemma sg10360 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg6942

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29114_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10360

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29114_oai := @OAI.UniversalTensorSquare.sg29114_oai
