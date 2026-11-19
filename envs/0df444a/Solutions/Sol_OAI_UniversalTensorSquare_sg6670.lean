-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6670
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:05:55.864141+00:00
-- url     : https://prove2.me/submissions/f9402e02-56d1-4a32-9651-75692c438c8a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1038
import Theorems.Thm_OAI_UniversalTensorSquare_sg940
import Definitions.Def_OAIQ259US001
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

lemma sg6670_oai : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1038

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6670_oai := @OAI.UniversalTensorSquare.sg6670_oai
