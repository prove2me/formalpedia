-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27728
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T13:58:23.884571+00:00
-- url     : https://prove2.me/submissions/89a4f92b-5dec-4cd0-bca2-427346f848f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1328
import Theorems.Thm_OAI_UniversalTensorSquare_sg1334
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

lemma sg10199 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1334

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 67. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27728_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10199

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27728_oai := @OAI.UniversalTensorSquare.sg27728_oai
