-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12023
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:38:49.785625+00:00
-- url     : https://prove2.me/submissions/a7ed4ae9-2278-4ef4-b4e2-3c0a64e2cb30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg765
import Theorems.Thm_OAI_UniversalTensorSquare_sg958

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

lemma sg7472 : RowSquare [6,4,2,2,2,2,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg958 sg765

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12023_oai : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7472

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12023_oai := @OAI.UniversalTensorSquare.sg12023_oai
