-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25182
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:45:05.805377+00:00
-- url     : https://prove2.me/submissions/c607e584-e94e-4bf0-ae3e-015d447ad466
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1378
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8254 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1378

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10845 : RowSquare [7,5,2,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2702

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25182_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8254 sg10845

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25182_oai := @OAI.UniversalTensorSquare.sg25182_oai
