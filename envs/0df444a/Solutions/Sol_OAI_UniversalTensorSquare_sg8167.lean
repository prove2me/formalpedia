-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8167
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:11:40.820247+00:00
-- url     : https://prove2.me/submissions/0ff6a3a2-76da-48f7-bf92-ac6c6e9db870

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg334
import Theorems.Thm_OAI_UniversalTensorSquare_sg373

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2319 : RowSquare [7,3,2,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg334

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

lemma sg8167_oai : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg373 sg2319

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8167_oai := @OAI.UniversalTensorSquare.sg8167_oai
