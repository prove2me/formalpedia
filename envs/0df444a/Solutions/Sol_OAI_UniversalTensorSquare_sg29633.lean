-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29633
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:50:18.27481+00:00
-- url     : https://prove2.me/submissions/4ffae4f1-a307-4eb5-80b5-1f75bd911de4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg6937
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

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

lemma sg10353 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6937

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 72. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29633_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10353

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29633_oai := @OAI.UniversalTensorSquare.sg29633_oai
