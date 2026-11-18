-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4736
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:27:55.622269+00:00
-- url     : https://prove2.me/submissions/a1fc5d17-ae12-4322-91f0-3304d2e5973a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg33

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4736_oai : RowSquare [5,3,3,2,1,1,1,1] [3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg1682

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4736_oai := @OAI.UniversalTensorSquare.sg4736_oai
