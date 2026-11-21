-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8441
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:17:41.639209+00:00
-- url     : https://prove2.me/submissions/21e2135e-c97a-4e46-8ebc-6ab92ee75beb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg849
import Theorems.Thm_OAI_UniversalTensorSquare_sg998
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6880 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg849 sg998

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg8441_oai : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6880

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8441_oai := @OAI.UniversalTensorSquare.sg8441_oai
