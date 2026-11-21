-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6768
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:09:05.423351+00:00
-- url     : https://prove2.me/submissions/2cf48551-bec6-4334-9bec-dbbd11ae69ce

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg587

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

lemma sg6768_oai : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1416

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6768_oai := @OAI.UniversalTensorSquare.sg6768_oai
