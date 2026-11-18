-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40607
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:55:51.335174+00:00
-- url     : https://prove2.me/submissions/c28d8e58-33ed-435a-add4-845808d5f36f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg13764
import Theorems.Thm_OAI_UniversalTensorSquare_sg20529

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17386 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13764

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 100. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40607_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,7,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17386

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40607_oai := @OAI.UniversalTensorSquare.sg40607_oai
