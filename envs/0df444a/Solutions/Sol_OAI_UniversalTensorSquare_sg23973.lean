-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23973
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:16:13.505636+00:00
-- url     : https://prove2.me/submissions/9be120be-e991-4094-b24d-249576b2ff16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10617
import Theorems.Thm_OAI_UniversalTensorSquare_sg1687
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sg8351 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1687

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23973_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8351 sg10617

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23973_oai := @OAI.UniversalTensorSquare.sg23973_oai
