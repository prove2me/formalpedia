-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8429
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:17:17.275204+00:00
-- url     : https://prove2.me/submissions/2e0f5554-13e9-47a1-9663-0cf4e2ee79a8

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1332
import Theorems.Thm_OAI_UniversalTensorSquare_sg849
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

lemma sg8429_oai : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1332

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8429_oai := @OAI.UniversalTensorSquare.sg8429_oai
