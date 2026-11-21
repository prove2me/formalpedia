-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34914
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:24:13.774016+00:00
-- url     : https://prove2.me/submissions/98d45c37-db15-4b36-8ebf-f9cb035f7e11

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17335
import Theorems.Thm_OAI_UniversalTensorSquare_sg20510

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 85. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34914_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17335

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34914_oai := @OAI.UniversalTensorSquare.sg34914_oai
