-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24709
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:34:18.445905+00:00
-- url     : https://prove2.me/submissions/9e0b90ee-ed20-48a1-9197-727351ffe2e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Theorems.Thm_OAI_UniversalTensorSquare_sg9752

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8650 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24709_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9752

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24709_oai := @OAI.UniversalTensorSquare.sg24709_oai
