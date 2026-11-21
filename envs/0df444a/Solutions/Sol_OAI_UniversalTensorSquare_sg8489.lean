-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8489
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:22:07.965601+00:00
-- url     : https://prove2.me/submissions/9ca6191b-2ac7-47fe-a1f8-a91600c2cb9e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg615
import Theorems.Thm_OAI_UniversalTensorSquare_sg636
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5124 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg636 sg615

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

lemma sg8489_oai : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5124

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8489_oai := @OAI.UniversalTensorSquare.sg8489_oai
