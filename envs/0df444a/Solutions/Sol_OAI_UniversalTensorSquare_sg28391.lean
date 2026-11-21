-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28391
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T14:33:23.63113+00:00
-- url     : https://prove2.me/submissions/7b30fd8a-cdbf-464d-b3e8-9b2525487c23

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10260
import Theorems.Thm_OAI_UniversalTensorSquare_sg8434

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28391_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10260

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28391_oai := @OAI.UniversalTensorSquare.sg28391_oai
