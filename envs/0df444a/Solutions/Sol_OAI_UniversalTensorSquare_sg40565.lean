-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40565
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:55:04.086504+00:00
-- url     : https://prove2.me/submissions/a83b1cdc-f75c-4aa5-ad7a-a054c4c0aaa6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg20529
import Theorems.Thm_OAI_UniversalTensorSquare_sg2372
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg312

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4317 : RowSquare [7,4,3,1,1] [3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg306 sg312

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14890 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2372 sg4317

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg17382 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14890

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

lemma sg40565_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,6,6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17382

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40565_oai := @OAI.UniversalTensorSquare.sg40565_oai
