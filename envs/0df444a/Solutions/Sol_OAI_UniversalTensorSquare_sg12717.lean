-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12717
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:45:25.749483+00:00
-- url     : https://prove2.me/submissions/51159745-bee8-4af2-ac48-ea9dc75e2c4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg165
import Theorems.Thm_OAI_UniversalTensorSquare_sg179

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg316 : RowSquare [4,1,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg179

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5560 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg316 sg1001

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12717_oai : RowSquare [10,3,2,2,2,2,2,2] [7,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg5560

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12717_oai := @OAI.UniversalTensorSquare.sg12717_oai
