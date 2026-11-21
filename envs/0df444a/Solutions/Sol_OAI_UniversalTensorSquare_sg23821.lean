-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23821
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:38:24.293043+00:00
-- url     : https://prove2.me/submissions/95458dae-b7ef-4a67-9d34-2ed3a972b2d1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10625
import Theorems.Thm_OAI_UniversalTensorSquare_sg8345

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

lemma sg23821_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10625

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23821_oai := @OAI.UniversalTensorSquare.sg23821_oai
