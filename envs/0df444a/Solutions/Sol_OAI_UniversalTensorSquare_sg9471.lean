-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9471
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:52:32.698264+00:00
-- url     : https://prove2.me/submissions/3961b3e9-4cca-4bd5-8fa1-81a7397dff5e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1429

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9471_oai : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1429

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9471_oai := @OAI.UniversalTensorSquare.sg9471_oai
